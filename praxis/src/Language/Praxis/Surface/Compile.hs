{-# LANGUAGE OverloadedStrings #-}

{- |
Functions defined by clauses, compiled to primitive recursive definitions,
and their unfolding lemmas.

A function is type-erased: a PRF on codes.  Its clauses split on the
constructors of one argument, the scrutinee, each constructor once; a split
is a dispatch on the tag, @if hd c == 0 then … else if hd c == 1 then … else
0@, so a code outside the type falls through to 0, and a pattern variable of
a field is its projection.  A function whose clauses call it is recursive on
the scrutinee, structurally: every recursive call passes a field of the
scrutinee's constructor there, and the other arguments unchanged.  It is then
an instance of the prelude's course-of-values recursion,

> f a₀ … = cvrec {λ k h ȳ. dispatch on k} a_c ȳ

its recursive calls looked up in the history, @at h k (field k)@.

Every clause is an unfolding lemma, named @f.unfold-C@ (and @f.eq_i@), an
equation which holds for all codes, since the dispatch reads the tag and the
fields only.  Its proof is generated: a chain of instances of lemmas proved
over variables — the definition, the course-of-values step, the tag, the
collapse of the dispatch, the fields, the history — each certified by the
core; see "Language.Praxis.Surface.Encode" for why definitional equality is
never used on the codes of constructors themselves.
-}
module Language.Praxis.Surface.Compile (
  Compiled (..),
  compileFunction,
  functionLemma,
) where

import Bound (Scope, Var (..), fromScope)
import Control.Monad (forM, unless, when)
import Data.List (nub)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (fromDec, fromText, runBuilder)
import Data.Void (Void, absurd)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (collapseLemma, ctorLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))

-- | A function in the core: its definition, and its lemmas with their declarations, in order.
data Compiled = Compiled
  { compiledEquations :: ![Text]
  , compiledLemmas :: ![(Text, Text)]
  , compiledUnfoldings :: ![(Text, CT, CT)]
  -- ^ each unfolding lemma, with its sides
  }

raw :: Segment -> Text
raw = \case
  Ident t -> t
  Op t -> t

-- | The core name of a lemma of a function: @f.#def@, @f.unfold-Nil@, …
functionLemma :: FunInfo -> Text -> Text
functionLemma f n = mangleGlobal (map raw (funQual f) <> [n])

-- | Where a pattern variable is: an argument itself, or a field of the scrutinee's constructor.
data Place = Arg !Int | Field !Int
  deriving stock (Eq, Show)

-- | The places of a clause's variables, in the order they are numbered.
places :: [Pattern] -> Either String [Place]
places = fmap concat . traverse one . zip [0 ..]
  where
    one (i, p) = case p of
      PVar _ -> Right [Arg i]
      PWild -> Right []
      PCon _ subs -> concat <$> traverse field (zip [0 ..] subs)
      _ -> Left "numeral and successor patterns are not supported yet"
    field (j, p) = case p of
      PVar _ -> Right [Field j]
      PWild -> Right []
      _ -> Left "nested patterns are not supported yet"

compileFunction :: Env -> FunDef -> Either String Compiled
compileFunction env fd = do
  let info = fdInfo fd
      core = funCore info
      arity = length (fdArgs fd)
      clauses = fdClauses fd
      columns = nub [i | fc <- clauses, (i, PCon {}) <- zip [0 ..] (fcPatterns fc)]
      names = unfoldingNames env (map fcPatterns clauses)
      argName i = "a" <> T.pack (show i)
      args = map (CVar . argName) [0 .. arity - 1]
      vargs = map (CVar . ("v_" <>) . argName) [0 .. arity - 1]
  when (null clauses) $ Left "a function with no clauses"
  case columns of
    [] -> do
      -- No case analysis: one clause, and no recursion.
      fc <- case clauses of
        [fc] -> Right fc
        _ -> Left "several clauses, none of which matches on a constructor"
      ps <- places (fcPatterns fc)
      when (callsSelf core (fcBody fc)) $ Left "a recursive function must match on a constructor of the argument it recurses on"
      body <- bodyCT core (\i -> args !! argIndex ps i) (const (Left "unreachable")) fc
      let eqn = definition core (map argName [0 .. arity - 1]) body
      rhs <- clauseRhs ps fc
      let triples = [(CSym core (patternArgs ps fc), rhs, "refl")]
      pure (Compiled [eqn] (unfoldings info names triples) (table info names triples))
    [c] -> do
      let ctorRefs = [r | fc <- clauses, PCon r _ <- [fcPatterns fc !! c]]
      ctorsSeen <- forM ctorRefs \(Ref _ r) -> maybe (Left "internal: an unknown constructor") Right (ctorByCore env r)
      dat <- case ctorsSeen of
        ci : _ -> maybe (Left "internal: a constructor of no data type") Right (dataOfCtor env ci)
        [] -> Left "internal: no constructor"
      let ctors = dataCtors dat
      unless (length clauses == length ctors && all (\ci -> length [() | cj <- ctorsSeen, ctorCore cj == ctorCore ci] == 1) ctors) $
        Left "the clauses must match each constructor of the scrutinee's type exactly once (no overlap, no catch-all) for now"
      forM_' clauses \fc -> unless (all (\(i, p) -> i == c || isVar p) (zip [0 ..] (fcPatterns fc))) (Left "only one argument may be matched on, for now")
      infos <- forM clauses \fc -> do
        ps <- places (fcPatterns fc)
        ci <- case fcPatterns fc !! c of
          PCon (Ref _ r) _ -> maybe (Left "internal") Right (ctorByCore env r)
          _ -> Left "internal"
        pure (fc, ps, ci)
      let recursive = any (\(fc, _, _) -> callsSelf core (fcBody fc)) infos
          others = [i | i <- [0 .. arity - 1], i /= c]
          byIndex = [(ctorIndex ci, x) | x@(_, _, ci) <- infos]
          ordered = [x | i <- [0 .. length ctors - 1], Just x <- [lookup i byIndex]]
      if not recursive
        then do
          branches <- forM ordered \(fc, ps, _) ->
            bodyCT core (placeCT (args !! c) (\i -> args !! i) ps) (const (Left "unreachable")) fc
          let dispatch = ifChain (hdT (args !! c)) branches
              defLemma = functionLemma info "#def"
              dispatchAt scr others' = ifChain (hdT scr) [either (error "internal") id (bodyCT core (placeCT scr others' ps) (const (Left "")) fc) | (fc, ps, _) <- ordered]
          proofs <- forM ordered \(fc, ps, ci) -> do
            rhs <- clauseRhs ps fc
            let scr = CSym (ctorCore ci) (fieldVars ps fc ci)
                lhs = CSym core (patternArgs ps fc)
                start = dispatchAt scr (argVar ps fc)
                tagged = replaceCT (\t -> if t == hdT scr then Just (CNum (fromIntegral (ctorIndex ci))) else Nothing) start
                branch = branchAt scr ps fc
                steps =
                  [(start, "exact " <> fromText defLemma), (tagged, "cong " <> fromText (ctorLemma ci "tag")), (branch, "exact " <> fromText (collapseLemma dat (ctorIndex ci)))]
                    <> fieldSteps ci scr (fieldVars ps fc ci) branch
            pure (lhs, rhs, calc lhs steps)
          pure (Compiled [definition core (map argName [0 .. arity - 1]) dispatch] ((defLemma, theorem defLemma (equation (CSym core vargs) (ifChain (hdT (vargs !! c)) [either (error "internal") id (bodyCT core (placeCT (vargs !! c) (vargs !!) ps) (const (Left "")) fc) | (fc, ps, _) <- ordered])) "refl") : unfoldings info names proofs) (table info names proofs))
        else do
          -- Course-of-values recursion on column c: the λ takes k, h and the other arguments.
          let lamParams = ["k", "h"] <> map argName others
              other i = CVar (argName i)
              recCall ps fc k h callArgs = recursiveCall c others ps fc k h callArgs
          branches <- forM ordered \(fc, ps, _) ->
            bodyCT core (placeCT (CVar "k") other ps) (recCall ps fc (CVar "k") (CVar "h")) fc
          let lam = runBuilder ("{λ " <> unwordsB (map fromText lamParams) <> ". " <> render (ifChain (hdT (CVar "k")) branches) <> "}")
              cvrec scr rest = CRaw (runBuilder ("cvrec " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              hist scr rest = CRaw (runBuilder ("hist " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              defLemma = functionLemma info "#def"
              betaLemma = functionLemma info "#beta"
              vothers = map (vargs !!) others
              stepAt scr rest ps fc = either (error "internal") id (bodyCT core (placeCT scr (\i -> rest !! position others i) ps) (recursiveCall c others ps fc scr (hist scr rest)) fc)
              betaBody scr rest = ifChain (hdT scr) [stepAt scr rest ps fc | (fc, ps, _) <- ordered]
          proofs <- forM ordered \(fc, ps, ci) -> do
            rhs <- clauseRhs ps fc
            let fields = fieldVars ps fc ci
                scr = CSym (ctorCore ci) fields
                rest = [argVar ps fc i | i <- others]
                h = hist scr rest
                lhs = CSym core (patternArgs ps fc)
                start = betaBody scr rest
                tagged = replaceCT (\t -> if t == hdT scr then Just (CNum (fromIntegral (ctorIndex ci))) else Nothing) start
                branch = stepAt scr rest ps fc
                afterFields = foldl (\t (j, x) -> replaceCT (\u -> if u == fieldT j scr then Just x else Nothing) t) branch (zip [0 ..] fields)
                recFields = nub (recursiveFields ps fc)
                histSteps =
                  scanl1'
                    [ (j, replaceCT (\u -> if u == CSym "at" [h, scr, fields !! j] then Just (cvrec (fields !! j) rest) else Nothing))
                    | j <- recFields
                    ]
                    afterFields
                defSteps = scanl1' [(j, replaceCT (\u -> if u == cvrec (fields !! j) rest then Just (CSym core (argsWith c (fields !! j) rest)) else Nothing)) | j <- recFields] (lastOf afterFields histSteps)
                haves =
                  mconcat
                    [ "have L"
                        <> fromDec j
                        <> ": ((lt "
                        <> render (fields !! j)
                        <> " "
                        <> render scr
                        <> ") = 1) { exact "
                        <> fromText (ctorLemma ci ("lt-" <> T.pack (show j)))
                        <> " }; have E"
                        <> fromDec j
                        <> ": ("
                        <> render (CSym "at" [h, scr, fields !! j])
                        <> " = "
                        <> render (cvrec (fields !! j) rest)
                        <> ") { exact histAt }; "
                    | j <- recFields
                    ]
                steps =
                  [(cvrec scr rest, "exact " <> fromText defLemma), (start, "exact " <> fromText betaLemma), (tagged, "cong " <> fromText (ctorLemma ci "tag")), (branch, "exact " <> fromText (collapseLemma dat (ctorIndex ci)))]
                    <> fieldSteps ci scr fields branch
                    <> [(t, "cong E" <> fromDec j) | (j, t) <- histSteps]
                    <> [(t, "cong " <> fromText defLemma) | (_, t) <- defSteps]
            pure (lhs, rhs, haves <> calc lhs steps)
          pure
            ( Compiled
                [definition core (map argName [0 .. arity - 1]) (cvrec (args !! c) (map (args !!) others))]
                ( (defLemma, theorem defLemma (equation (CSym core vargs) (cvrec (vargs !! c) vothers)) "refl")
                    : (betaLemma, theorem betaLemma (equation (cvrec (vargs !! c) vothers) (betaBody (vargs !! c) vothers)) "refl")
                    : unfoldings info names proofs
                )
                (table info names proofs)
            )
    _ -> Left "clauses matching on several arguments are not supported yet"
  where
    snd' (a, b) = (a, b)
    forM_' xs f = mapM_ f xs
    isVar = \case
      PVar _ -> True
      PWild -> True
      _ -> False
    position xs i = length (takeWhile (/= i) xs)
    lastOf d = \case
      [] -> d
      xs -> snd (last xs)
    -- Each step of a chain of rewrites, starting from a term.
    scanl1' rewrites t0 = drop 1 (scanl (\(_, t) (j, f) -> (j, f t)) (0, t0) rewrites)
    argsWith c x rest = let (before, after) = splitAt c rest in before <> [x] <> after
    definition core params body = runBuilder (unwordsB (map fromText (core : params)) <> " = " <> render body)
    equation lhs rhs = "(" <> render lhs <> " = " <> render rhs <> ")"
    theorem name stmt proof = runBuilder ("theorem " <> fromText name <> " : |- " <> stmt <> "\nby " <> proof)
    calc lhs steps = "calc " <> render lhs <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps]
    unfoldings info names triples =
      concat
        [ [ (functionLemma info n, theorem (functionLemma info n) stmt proof)
          , (functionLemma info alias, theorem (functionLemma info alias) stmt ("exact " <> fromText (functionLemma info n)))
          ]
        | (i, n, (lhs, rhs, proof)) <- zip3 [1 :: Int ..] names triples
        , let alias = "eq_" <> T.pack (show i)
              stmt = equation lhs rhs
        ]

    -- The clause's variables as core variables, by their names.
    varOf fc i = CVar (mangleVariable (fst (fcVars fc !! i)))
    argVar ps fc i = case [j | (j, Arg a) <- zip [0 ..] ps, a == i] of
      j : _ -> varOf fc j
      [] -> CVar ("v__x23_" <> T.pack (show i))
    fieldVars ps fc ci = [maybe (CVar ("v__x23_f" <> T.pack (show j))) (varOf fc) (lookup (Field j) (zip ps [0 ..])) | j <- [0 .. length (ctorFields ci) - 1]]
    patternArgs ps fc = [case p of PCon (Ref _ r) _ -> maybe (CVar "?") (\ci -> CSym (ctorCore ci) (fieldVars ps fc ci)) (ctorByCore env r); _ -> argVar ps fc i | (i, p) <- zip [0 ..] (fcPatterns fc)]
    clauseRhs ps fc = bodyCT (funCore (fdInfo fd)) (\i -> varOf fc i) (\callArgs -> Right (CSym (funCore (fdInfo fd)) (map snd callArgs))) fc <* pure ps
    table info names triples = [(functionLemma info n, lhs, rhs) | (n, (lhs, rhs, _)) <- zip names triples]
    argIndex ps i = case ps !! i of
      Arg a -> a
      Field _ -> 0
    placeCT scr other ps i = case ps !! i of
      Arg a -> other a
      Field j -> fieldT j scr
    branchAt scr ps fc = either (error "internal") id (bodyCT (funCore (fdInfo fd)) (placeCT scr (argVar ps fc) ps) (const (Left "")) fc)
    fieldSteps ci scr fields branch =
      drop 1 $
        scanl
          (\(t, _) (j, x) -> (replaceCT (\u -> if u == fieldT j scr then Just x else Nothing) t, "cong " <> fromText (ctorLemma ci ("field-" <> T.pack (show j)))))
          (branch, "")
          [(j, x) | (j, x) <- zip [0 ..] fields, fieldT j scr `occursIn` branch]
    occursIn needle = \case
      t | t == needle -> True
      CSym _ as -> any (occursIn needle) as
      _ -> False
    -- The fields the recursive calls of a clause are on.
    recursiveFields ps fc = mapMaybe (\case (Field j, True) -> Just j; _ -> Nothing) [(p, i `elem` recVars (funCore (fdInfo fd)) fc) | (i, p) <- zip [0 ..] ps]
    -- A recursive call: on a field of the scrutinee, the other arguments unchanged.
    recursiveCall c others ps _fc k h callArgs = do
      unless (length callArgs == length others + 1) $ Left "a recursive call with the wrong number of arguments"
      field <- case fst (callArgs !! c) of
        Just i | Field j <- ps !! i -> Right j
        _ -> Left "a recursive call must pass a field of the matched constructor where the function matches"
      forM_' [(i, a) | (i, (a, _)) <- zip [0 ..] callArgs, i /= c] \(i, a) -> case (a, [j | (j, Arg x) <- zip [0 ..] ps, x == i]) of
        (Just v, [j]) | v == j -> Right ()
        _ -> Left "a recursive call must pass the other arguments unchanged (primitive recursion)"
      Right (CSym "at" [h, k, fieldT field k])

-- | Whether a body calls the function.
callsSelf :: Text -> Scope Int Expr Void -> Bool
callsSelf core body = core `elem` [r | Global (Ref _ r) <- universe (fromScope body)]
  where
    universe e =
      e : case e of
        App f x -> universe f <> universe x
        At _ x -> universe x
        _ -> []

-- | The pattern variables of a clause which are arguments of its recursive calls.
recVars :: Text -> FunClause -> [Int]
recVars core fc = [i | Var (B i) <- concatMap snd' (calls (fromScope (fcBody fc)))]
  where
    snd' (_, as) = as
    calls e = case spine e of
      (Global (Ref _ r), as) | r == core -> [(r, map stripLocations as)] <> concatMap calls as
      (_, as) -> concatMap calls as

{- |
The core term of a clause's body: the variables by the function given, the
recursive calls by the other, their arguments already translated.
-}
bodyCT :: Text -> (Int -> CT) -> ([(Maybe Int, CT)] -> Either String CT) -> FunClause -> Either String CT
bodyCT core var rec fc = go (fromScope (fcBody fc))
  where
    go e = case spine e of
      (Var (B i), []) -> Right (var i)
      (Var (F v), _) -> absurd v
      (Global (Ref _ r), as)
        | r == core -> do
            cts <- traverse go as
            rec (zip (map variable as) cts)
        | otherwise -> CSym r <$> traverse go as
      (Nat n, []) -> Right (CNum n)
      _ -> Left "no core term for this expression"
    -- The pattern variable an argument is, when it is one.
    variable a = case stripLocations a of
      Var (B i) -> Just i
      _ -> Nothing
