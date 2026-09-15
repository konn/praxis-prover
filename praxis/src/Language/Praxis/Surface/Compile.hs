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

A function under constraints, @mconcat : Monoid a => List a -> a@, takes a
dictionary: the methods it uses of the classes constraining its type
parameters.  A method taking arguments is a parameter of the function's
schema, @w_1@, and a method taking none, a value, an argument after the
function's own, so that @mconcat xs@ is @mconcat {w_1} xs d0@ in the core.  A
recursive call passes the dictionary on unchanged, as primitive recursion
keeps the parameters of a schema.

Every clause is an unfolding lemma, named @f.unfold-C@ (and @f.eq_i@), an
equation which holds for all codes, since the dispatch reads the tag and the
fields only; for a function under constraints, a rule over the parameters of
its schema, its variables all metavariables, which an appeal instantiates at
the methods of instances.  Its proof is generated: a chain of instances of
lemmas proved over variables — the definition, the course-of-values step,
the tag, the collapse of the dispatch, the fields, the history — each
certified by the core; see "Language.Praxis.Surface.Encode" for why
definitional equality is never used on the codes of constructors themselves.
-}
module Language.Praxis.Surface.Compile (
  Compiled (..),
  compileFunction,
  functionLemma,
  dictionaryCT,
  ownDictionary,
  ruleBinders,
) where

import Bound (Scope, Var (..), fromScope)
import Control.Monad (forM, unless, when)
import Data.List (nub)
import Data.Maybe (catMaybes, fromMaybe, listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Data.Void (Void, absurd)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (collapseLemma, ctorLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Language.Praxis.Surface.Types (Ty (TNat))
import Text.Read (readMaybe)

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

{- |
A dictionary as a call in a lemma passes it on: the parameters of the
function's schema, in braces, and the variables of its values, in the order
of its places.
-}
dictionaryCT :: [Slot] -> [CT]
dictionaryCT = go 1 (0 :: Int)
  where
    go _ _ [] = []
    go j k (s : ss)
      | slotArity s > 0 = CStatic (staticName j) : go (j + 1) k ss
      | otherwise = CVar (valueVar (T.pack (show k))) : go j (k + 1) ss

-- | The dictionary of a function as its recursive calls pass it on: its own parameters and values, in order.
ownDictionary :: [Slot] -> [Expr a]
ownDictionary = go 1 (0 :: Int)
  where
    go _ _ [] = []
    go j k (s : ss)
      | slotArity s > 0 = Global (Ref RefStatic (staticName j)) : go (j + 1) k ss
      | otherwise = Global (Ref RefValueParam (T.pack (show k))) : go j (k + 1) ss

argName :: Int -> Text
argName i = "a" <> T.pack (show i)

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
      -- 0 binds nothing; the successor its predecessor, the one field of a value of Nat.
      PNat 0 -> Right []
      PSucc sub -> field (0, sub)
      -- An absurd pattern binds nothing: the clause is never reached.
      PAbsurd -> Right []
      _ -> Left "a numeral other than 0 in a pattern: write it S n"
    field (j, p) = case p of
      PVar _ -> Right [Field j]
      PWild -> Right []
      _ -> Left "nested patterns are not supported yet"

compileFunction :: Env -> FunDef -> Either String Compiled
compileFunction env fd = do
  let columns = nub [i | fc <- clauses, (i, p) <- zip [0 ..] (fcPatterns fc), matchesOn p]
  when (null clauses) $ Left "a function with no clauses"
  case columns of
    [] -> do
      -- No case analysis: one clause, and no recursion.
      fc <- case clauses of
        [fc] -> Right fc
        _ -> Left "several clauses, none of which matches on a constructor"
      ps <- places (fcPatterns fc)
      when (callsSelf core (fcBody fc)) $ Left "a recursive function must match on a constructor of the argument it recurses on"
      b <- body (\i -> args !! argIndex ps i) inDef (const (Left "unreachable")) fc
      rhs <- clauseRhs ps fc
      let triples = [(CSym core (patternArgs ps fc <> dict), rhs, "refl")]
      pure (Compiled [definition b] (unfoldings triples) (table triples))
    [c] | fdArgs fd !! c == TNat -> natColumn c
    [c] -> do
      let ctorRefs = [r | fc <- clauses, PCon r _ <- [fcPatterns fc !! c]]
      ctorsSeen <- forM ctorRefs \(Ref _ r) -> maybe (Left "internal: an unknown constructor") Right (ctorByCore env r)
      dat <- case ctorsSeen of
        ci : _ -> maybe (Left "internal: a constructor of no data type") Right (dataOfCtor env ci)
        [] -> Left "internal: no constructor"
      let ctors = dataCtors dat
      unless (all (\ci -> let k = length [() | cj <- ctorsSeen, ctorCore cj == ctorCore ci] in k == 1 || (k == 0 && ctorCore ci `elem` fdImpossible fd)) ctors) $
        Left "the clauses must match each constructor of the scrutinee's type exactly once, but those impossible at the indices of its signature (no overlap, no catch-all) for now"
      forM_' clauses \fc -> unless (all (\(i, p) -> i == c || isVar p) (zip [0 ..] (fcPatterns fc))) (Left "only one argument may be matched on, for now")
      infos <- forM clauses \fc -> do
        ps <- places (fcPatterns fc)
        ci <- case fcPatterns fc !! c of
          PCon (Ref _ r) _ -> maybe (Left "internal") Right (ctorByCore env r)
          _ -> Left "internal"
        pure (fc, ps, ci)
      let recursive = any (\(fc, _, _) -> callsSelf core (fcBody fc)) infos
          -- The other arguments: the function's own, then the values of its dictionary.
          others = [i | i <- [0 .. arity - 1], i /= c]
          userOthers = [i | i <- [0 .. userArity - 1], i /= c]
          byIndex = [(ctorIndex ci, x) | x@(_, _, ci) <- infos]
          orderedM = [lookup i byIndex | i <- [0 .. length ctors - 1]]
          ordered = catMaybes orderedM
          defLemma = functionLemma info "#def"
          defLhs = CSym core (take userArity vargs <> dict)
      if not recursive
        then do
          branches <- forM orderedM $ maybe (Right (CNum 0)) \(fc, ps, _) ->
            body (placeCT (args !! c) (\i -> args !! i) ps) inDef (const (Left "unreachable")) fc
          let dispatch = ifChain (hdT (args !! c)) branches
              dispatchAt scr others' = ifChain (hdT scr) [maybe (CNum 0) (\(fc, ps, _) -> either (error "internal") id (body (placeCT scr others' ps) inLemma (const (Left "")) fc)) m | m <- orderedM]
          proofs <- forM ordered \(fc, ps, ci) -> do
            rhs <- clauseRhs ps fc
            let scr = CSym (ctorCore ci) (fieldVars ps fc ci)
                lhs = CSym core (patternArgs ps fc <> dict)
                start = dispatchAt scr (argVar ps fc)
                tagged = replaceCT (\t -> if t == hdT scr then Just (CNum (fromIntegral (ctorIndex ci))) else Nothing) start
                branch = branchAt scr ps fc
                steps =
                  [(start, "exact " <> fromText defLemma), (tagged, "cong " <> fromText (ctorLemma ci "tag")), (branch, "exact " <> fromText (collapseLemma dat (ctorIndex ci)))]
                    <> fieldSteps ci scr (fieldVars ps fc ci) branch
            pure (lhs, rhs, calc lhs steps)
          pure (Compiled [definition dispatch] ((defLemma, lemma defLemma vargs defLhs (dispatchAt (vargs !! c) (vargs !!)) "refl") : unfoldings proofs) (table proofs))
        else do
          -- Course-of-values recursion on column c: the λ takes k, h and the other arguments.
          let lamParams = ["k", "h"] <> map argName others
              other i = CVar (argName i)
              recCall ps fc k h callArgs = recursiveCall c userOthers ps fc k h callArgs
          branches <- forM orderedM $ maybe (Right (CNum 0)) \(fc, ps, _) ->
            body (placeCT (CVar "k") other ps) inDef (recCall ps fc (CVar "k") (CVar "h")) fc
          let lam = runBuilder ("{λ " <> unwordsB (map fromText lamParams) <> ". " <> render (ifChain (hdT (CVar "k")) branches) <> "}")
              cvrec scr rest = CRaw (runBuilder ("cvrec " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              hist scr rest = CRaw (runBuilder ("hist " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              betaLemma = functionLemma info "#beta"
              vothers = map (vargs !!) others
              stepAt scr rest ps fc = either (error "internal") id (body (placeCT scr (\i -> rest !! position others i) ps) inLemma (recursiveCall c userOthers ps fc scr (hist scr rest)) fc)
              betaBody scr rest = ifChain (hdT scr) [maybe (CNum 0) (\(fc, ps, _) -> stepAt scr rest ps fc) m | m <- orderedM]
          proofs <- forM ordered \(fc, ps, ci) -> do
            rhs <- clauseRhs ps fc
            let fields = fieldVars ps fc ci
                scr = CSym (ctorCore ci) fields
                rest = [argVar ps fc i | i <- others]
                h = hist scr rest
                lhs = CSym core (patternArgs ps fc <> dict)
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
                recursiveAt x = CSym core (argsWith c x (take (userArity - 1) rest) <> dict)
                defSteps = scanl1' [(j, replaceCT (\u -> if u == cvrec (fields !! j) rest then Just (recursiveAt (fields !! j)) else Nothing)) | j <- recFields] (lastOf afterFields histSteps)
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
                [definition (cvrec (args !! c) (map (args !!) others))]
                ( (defLemma, lemma defLemma vargs defLhs (cvrec (vargs !! c) vothers) "refl")
                    : (betaLemma, lemma betaLemma vargs (cvrec (vargs !! c) vothers) (betaBody (vargs !! c) vothers) "refl")
                    : unfoldings proofs
                )
                (table proofs)
            )
    cs | all (\c -> fdArgs fd !! c == TNat) cs -> natColumns cs
    _ -> Left "clauses matching on several arguments, not all of Nat, are not supported yet"
  where
    info = fdInfo fd
    core = funCore info
    slots = funSlots info
    statics = staticSlots slots
    userArity = length (fdArgs fd)
    -- The arguments of the definition: the function's own, then the values of its dictionary.
    arity = userArity + length (valueSlots slots)
    clauses = fdClauses fd
    names = unfoldingNames env (map fcPatterns clauses)
    args = map (CVar . argName) [0 .. arity - 1]
    -- The variables of a lemma: the arguments, and the values of the dictionary.
    vargs = map lemmaVar [0 .. arity - 1]
    lemmaVar i
      | i < userArity = CVar ("v_" <> argName i)
      | otherwise = CVar (valueVar (T.pack (show (i - userArity))))
    dict = dictionaryCT slots
    body = bodyCT info userArity
    -- The values of the dictionary: arguments of the definition, variables of a lemma.
    inDef = CVar . argName . (userArity +)
    inLemma = CVar . valueVar . T.pack . show

    -- A pattern clauses are told apart by: a constructor, 0, or a successor.
    matchesOn = \case
      PCon {} -> True
      PNat _ -> True
      PSucc _ -> True
      _ -> False

    {- Matching on a value of Nat, in column c: a clause for 0 and one for S n,
    told apart by the sign of the value, the predecessor the field; recursion
    at the predecessor is course-of-values recursion on the value, as on a
    code.  The unfolding lemmas are proved as a constructor's are, the tag, the
    collapse and the field by the definitions of sgn and prd. -}
    natColumn c = do
      let isZero fc = case fcPatterns fc !! c of
            PNat 0 -> True
            _ -> False
          isSucc fc = case fcPatterns fc !! c of
            PSucc _ -> True
            _ -> False
      (zeroC, succC) <- case (filter isZero clauses, filter isSucc clauses) of
        ([z], [s]) | length clauses == 2 -> Right (z, s)
        _ -> Left "the clauses must match 0 and S n, each exactly once (no overlap, no catch-all) for now"
      forM_' clauses \fc -> unless (all (\(i, p) -> i == c || isVar p) (zip [0 ..] (fcPatterns fc))) (Left "only one argument may be matched on, for now")
      psZ <- places (fcPatterns zeroC)
      psS <- places (fcPatterns succC)
      let placesOf fc = if isZero fc then psZ else psS
          recursive = callsSelf core (fcBody zeroC) || callsSelf core (fcBody succC)
          others = [i | i <- [0 .. arity - 1], i /= c]
          userOthers = [i | i <- [0 .. userArity - 1], i /= c]
          defLemma = functionLemma info "#def"
          defLhs = CSym core (take userArity vargs <> dict)
          sgnT x = CSym "sgn" [x]
          natPlace scr other ps i = case ps !! i of
            Arg a -> other a
            Field _ -> CSym "prd" [scr]
          scrOf fc = if isZero fc then CNum 0 else CSym "S" [natFieldVar (placesOf fc) fc]
      if not recursive
        then do
          b0 <- body (natPlace (args !! c) (args !!) psZ) inDef (const (Left "unreachable")) zeroC
          bS <- body (natPlace (args !! c) (args !!) psS) inDef (const (Left "unreachable")) succC
          let at' scr others' ps fc = either (error "internal") id (body (natPlace scr others' ps) inLemma (const (Left "")) fc)
              dispatchAt scr others' = ifChain (sgnT scr) [at' scr others' psZ zeroC, at' scr others' psS succC]
          proofs <- forM clauses \fc -> do
            let ps = placesOf fc
            rhs <- clauseRhs ps fc
            let lhs = CSym core (patternArgs ps fc <> dict)
            pure (lhs, rhs, calc lhs [(dispatchAt (scrOf fc) (argVar ps fc), "exact " <> fromText defLemma), (rhs, "refl")])
          pure (Compiled [definition (ifChain (sgnT (args !! c)) [b0, bS])] ((defLemma, lemma defLemma vargs defLhs (dispatchAt (vargs !! c) (vargs !!)) "refl") : unfoldings proofs) (table proofs))
        else do
          let lamParams = ["k", "h"] <> map argName others
              other i = CVar (argName i)
          b0 <- body (natPlace (CVar "k") other psZ) inDef (recursiveCall c userOthers psZ zeroC (CVar "k") (CVar "h")) zeroC
          bS <- body (natPlace (CVar "k") other psS) inDef (recursiveCall c userOthers psS succC (CVar "k") (CVar "h")) succC
          let lam = runBuilder ("{λ " <> unwordsB (map fromText lamParams) <> ". " <> render (ifChain (sgnT (CVar "k")) [b0, bS]) <> "}")
              cvrec scr rest = CRaw (runBuilder ("cvrec " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              hist scr rest = CRaw (runBuilder ("hist " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
              betaLemma = functionLemma info "#beta"
              vothers = map (vargs !!) others
              stepAt scr rest ps fc = either (error "internal") id (body (natPlace scr (\i -> rest !! position others i) ps) inLemma (recursiveCall c userOthers ps fc scr (hist scr rest)) fc)
              betaBody scr rest = ifChain (sgnT scr) [stepAt scr rest psZ zeroC, stepAt scr rest psS succC]
          proofs <- forM clauses \fc -> do
            let ps = placesOf fc
            rhs <- clauseRhs ps fc
            let n = natFieldVar ps fc
                scr = scrOf fc
                rest = [argVar ps fc i | i <- others]
                h = hist scr rest
                lhs = CSym core (patternArgs ps fc <> dict)
                -- The branch at the value, the predecessor of a successor its variable.
                branch = replaceCT (\u -> if u == CSym "prd" [scr] then Just n else Nothing) (stepAt scr rest ps fc)
                recursiveHere = not (isZero fc) && callsSelf core (fcBody fc)
                viaHist = replaceCT (\u -> if u == CSym "at" [h, scr, n] then Just (cvrec n rest) else Nothing) branch
                viaDef = replaceCT (\u -> if u == cvrec n rest then Just (CSym core (argsWith c n (take (userArity - 1) rest) <> dict)) else Nothing) viaHist
                haves
                  | recursiveHere = "have L: ((lt " <> render n <> " " <> render scr <> ") = 1) { exact ltSucc }; have E: (" <> render (CSym "at" [h, scr, n]) <> " = " <> render (cvrec n rest) <> ") { exact histAt }; "
                  | otherwise = ""
                steps =
                  [(cvrec scr rest, "exact " <> fromText defLemma), (betaBody scr rest, "exact " <> fromText betaLemma), (branch, "refl")]
                    <> (if recursiveHere then [(viaHist, "cong E"), (viaDef, "cong " <> fromText defLemma)] else [])
            pure (lhs, rhs, haves <> calc lhs steps)
          pure
            ( Compiled
                [definition (cvrec (args !! c) (map (args !!) others))]
                ( (defLemma, lemma defLemma vargs defLhs (cvrec (vargs !! c) vothers) "refl")
                    : (betaLemma, lemma betaLemma vargs (cvrec (vargs !! c) vothers) (betaBody (vargs !! c) vothers) "refl")
                    : unfoldings proofs
                )
                (table proofs)
            )

    {- Matching on several values of Nat at once, in the columns given: each
    clause at 0, at S x, or at any value, in each; together the clauses cover
    each case, 0 or S, of the values once.  Recursion, at the predecessors of
    some of the values and at the others as they are, is course-of-values
    recursion on the code of their tuple, cons a₁ (cons a₂ … 0), each value
    its component.  An unfolding lemma for each case: the tuple taken apart
    by hdCons and tlCons, the dispatch collapsed by the definitions of sgn
    and prd, the history looked up by histAt, the tuple of the predecessors
    below the tuple by consLtL and consLtR. -}
    natColumns cs = do
      let kc = length cs
          colIdx = zip cs [0 :: Int ..]
          patAt fc c = fcPatterns fc !! c
          covers combo fc =
            and
              [ case patAt fc c of
                  PNat 0 -> not b
                  PSucc _ -> b
                  _ -> True
              | (c, b) <- zip cs combo
              ]
      forM_' clauses \fc -> unless (all (\(i, p) -> i `elem` cs || isVar p) (zip [0 ..] (fcPatterns fc))) (Left "the values not matched on are variables, for now")
      forM_' clauses \fc -> forM_' cs \c -> case patAt fc c of
        PSucc sub | not (isVar sub) -> Left "nested patterns are not supported yet"
        PNat j | j > 0 -> Left "a numeral other than 0 in a pattern: write it S n"
        _ -> Right ()
      cases <- forM (sequence (replicate kc [False, True])) \combo -> case filter (covers combo) clauses of
        [fc] -> Right (combo, fc)
        _ -> Left "the clauses must cover each case, 0 or S, of the values they match on exactly once (no overlap) for now"
      let others = [i | i <- [0 .. arity - 1], i `notElem` cs]
          userOthers = [i | i <- [0 .. userArity - 1], i `notElem` cs]
          defLemma = functionLemma info "#def"
          betaLemma = functionLemma info "#beta"
          defLhs = CSym core (take userArity vargs <> dict)
          component i t = hdT (iterate tlT t !! i)
          tupleT = foldr (\x acc -> CSym "cons" [x, acc]) (CNum 0)
          -- What each variable of a clause is: a value it matches whole (0), the predecessor of one (1), or another argument (2).
          roles fc =
            concat
              [ case p of
                  PVar _ -> [maybe (2, a) (\ci -> (0, ci)) (lookup a colIdx)]
                  PSucc (PVar _) -> [(1, fromMaybe 0 (lookup a colIdx))]
                  _ -> []
              | (a, p) <- zip [0 ..] (fcPatterns fc)
              ]
          roleOf fc v = listToMaybe (drop v (roles fc))
          roleTerm value other (r, j) = case r :: Int of
            0 -> value j
            1 -> CSym "prd" [value j]
            _ -> other j
          -- A recursive call, at the code k of the tuple and its history h: the history at the tuple of what it passes.
          recAt kT value hT fc callArgs = do
            unless (length callArgs == userArity) $
              Left ("a recursive call with " <> show (length callArgs) <> " arguments, where the function takes " <> show userArity)
            comps <- forM colIdx \(c, ci) -> case fst (callArgs !! c) >>= roleOf fc of
              Just (0, ci') | ci' == ci -> Right (False, value ci)
              Just (1, ci') | ci' == ci -> Right (True, CSym "prd" [value ci])
              _ -> Left "a recursive call passes each value the function matches on, or its predecessor"
            forM_' userOthers \a -> case fst (callArgs !! a) >>= roleOf fc of
              Just (2, a') | a' == a -> Right ()
              _ -> Left "a recursive call must pass the other arguments unchanged (primitive recursion)"
            unless (any fst comps) $ Left "a recursive call must pass the predecessor of a value the function matches on"
            Right (CSym "at" [hT, kT, tupleT (map snd comps)])
          -- A clause's body at the code k of the tuple, its values, its history h, the other arguments and the dictionary's values.
          bodyAt kT value hT other dv fc = body (\v -> maybe (CVar "?") (roleTerm value other) (roleOf fc v)) dv (recAt kT value hT fc) fc
          tree value leaf = go 0 []
            where
              go i combo
                | i == kc = leaf combo
                | otherwise = ifChain (CSym "sgn" [value i]) [go (i + 1) (combo <> [False]), go (i + 1) (combo <> [True])]
          lamParams = ["k", "h"] <> map argName others
      leavesDef <- forM cases \(combo, fc) -> (combo,) <$> bodyAt (CVar "k") (\ci -> component ci (CVar "k")) (CVar "h") (CVar . argName) inDef fc
      let lam = runBuilder ("{λ " <> unwordsB (map fromText lamParams) <> ". " <> render (tree (\ci -> component ci (CVar "k")) (\combo -> fromMaybe (CNum 0) (lookup combo leavesDef))) <> "}")
          cvrec scr rest = CRaw (runBuilder ("cvrec " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
          hist scr rest = CRaw (runBuilder ("hist " <> fromText lam <> " " <> unwordsB (map render (scr : rest))))
          vothers = map (vargs !!) others
          scrOf vs = tupleT [vs !! c | c <- cs]
          betaBody scr rest =
            let other a = rest !! position others a
             in tree (`component` scr) \combo -> case lookup combo cases of
                  Just fc -> either (error "internal") id (bodyAt scr (`component` scr) (hist scr rest) other inLemma fc)
                  Nothing -> CNum 0
      proofs <- forM cases \(combo, fc) -> do
        let rs = roles fc
            predVar ci = case [v | (v, (1, ci')) <- zip [0 ..] rs, ci' == ci] of
              v : _ -> varOf fc v
              [] -> CVar ("v__x23_c" <> T.pack (show ci))
            vals = [if b then CSym "S" [predVar ci] else CNum 0 | (ci, b) <- zip [0 ..] combo]
            otherArg a
              | a >= userArity = CVar (valueVar (T.pack (show (a - userArity))))
              | otherwise = case [v | (v, (2, a')) <- zip [0 ..] rs, a' == a] of
                  v : _ -> varOf fc v
                  [] -> CVar ("v__x23_" <> T.pack (show a))
            rest = map otherArg others
            scr = tupleT vals
            h = hist scr rest
            lhs = CSym core ([maybe (otherArg a) (vals !!) (lookup a colIdx) | a <- [0 .. userArity - 1]] <> dict)
            start = betaBody scr rest
            apart = takeApart start
            afterApart = maybe start fst (listToMaybe (reverse apart))
            caseTerm (r, j) = case r :: Int of
              0 -> vals !! j
              1 -> predVar j
              _ -> otherArg j
            -- The case's branch: its values, the predecessor of each S x its x.
            branch = replaceCT (\case CSym "prd" [CSym "S" [x]] -> Just x; _ -> Nothing) (either (error "internal") id (bodyAt scr (vals !!) h otherArg inLemma fc))
            lookups = nub [(u, tup) | u@(CSym "at" [h', k', tup]) <- subterms branch, h' == h, k' == scr]
            -- The tuple a recursive call looks up below the case's, component by component from the last.
            ltProof j tup =
              let comps' = untuple tup
                  nm p i = p <> T.pack (show (j :: Int)) <> "_" <> T.pack (show i)
                  suffix xs i = tupleT (drop i xs)
                  go i
                    | i >= kc = (False, "")
                    | otherwise =
                        let (lessTail, tailSteps) = go (i + 1)
                            c' = comps' !! i
                            c = vals !! i
                            tailLe
                              | lessTail = "have " <> fromText (nm "R" i) <> ": (" <> render (suffix comps' (i + 1)) <> " <= " <> render (suffix vals (i + 1)) <> ") { exact ltLe on " <> fromText (nm "Q" (i + 1)) <> " }; "
                              | otherwise = "have " <> fromText (nm "R" i) <> ": (" <> render (suffix vals (i + 1)) <> " <= " <> render (suffix vals (i + 1)) <> ") { exact leSelf }; "
                            fact = "have " <> fromText (nm "Q" i) <> ": (" <> render (suffix comps' i) <> " < " <> render (suffix vals i) <> ")"
                         in if c' /= c
                              then (True, tailSteps <> "have " <> fromText (nm "P" i) <> ": (" <> render c' <> " < " <> render c <> ") { exact ltSucc }; " <> tailLe <> fact <> " { exact consLtL on " <> fromText (nm "P" i) <> " " <> fromText (nm "R" i) <> " }; ")
                              else
                                if lessTail
                                  then (True, tailSteps <> "have " <> fromText (nm "P" i) <> ": (" <> render c <> " <= " <> render c <> ") { exact leSelf }; " <> fact <> " { exact consLtR on " <> fromText (nm "P" i) <> " " <> fromText (nm "Q" (i + 1)) <> " }; ")
                                  else (False, tailSteps)
               in snd (go 0)
            callOf tup = CSym core ([maybe (otherArg a) (untuple tup !!) (lookup a colIdx) | a <- [0 .. userArity - 1]] <> dict)
            haves = mconcat [ltProof j tup <> "have E" <> fromDec j <> ": (" <> render u <> " = " <> render (cvrec tup rest) <> ") { exact histAt }; " | (j, (u, tup)) <- zip [0 ..] lookups]
            histSteps = drop 1 (scanl (\(t, _) (j, (u, tup)) -> (replaceCT (\x -> if x == u then Just (cvrec tup rest) else Nothing) t, "cong E" <> fromDec j)) (branch, "") (zip [0 :: Int ..] lookups))
            afterHist = maybe branch fst (listToMaybe (reverse histSteps))
            defSteps = drop 1 (scanl (\(t, _) (_, tup) -> (replaceCT (\x -> if x == cvrec tup rest then Just (callOf tup) else Nothing) t, "cong " <> fromText defLemma)) (afterHist, "") lookups)
            steps =
              [(cvrec scr rest, "exact " <> fromText defLemma), (start, "exact " <> fromText betaLemma)]
                <> [(t, "cong " <> lem) | (t, lem) <- apart]
                <> [(t, "cong " <> lem) | (t, lem) <- collapsing afterApart]
                <> histSteps
                <> defSteps
        rhs <- body (\v -> maybe (CVar "?") caseTerm (roleOf fc v)) inLemma (\callArgs -> Right (CSym core (map snd callArgs <> dict))) fc
        pure (combo, (lhs, rhs, haves <> calc lhs steps))
      let named = [(functionLemma info ("unfold-" <> T.intercalate "-" [if b then "S" else "0" | b <- combo]), p) | (combo, p) <- proofs]
      pure
        ( Compiled
            [definition (cvrec (scrOf args) (map (args !!) others))]
            ( (defLemma, lemma defLemma vargs defLhs (cvrec (scrOf vargs) vothers) "refl")
                -- At a code of its own, so that its history is not computed out.
                : (betaLemma, lemma betaLemma (CVar "v_k" : vothers) (cvrec (CVar "v_k") vothers) (betaBody (CVar "v_k") vothers) "refl")
                : [(n, lemma n [l] l r p) | (n, (l, r, p)) <- named]
            )
            [(n, l, r) | (n, (l, r, _)) <- named]
        )

    -- A dispatch collapsed from its root, each node at a sign known by its lemma, then
    -- the predecessor of each successor: the codes and the history left as they are.
    collapsing t = case collapseAt t of
      Just (t', lem) -> (t', lem) : collapsing t'
      Nothing -> predSteps t
    collapseAt = \case
      CSym "ifte" [CSym "eq" [CSym "sgn" [v], CNum 0], a, CSym "ifte" [CSym "eq" [CSym "sgn" [v'], CNum 1], b, CNum 0]]
        | v == v', CNum 0 <- v -> Just (a, "collapseSgnZero")
        | v == v', CSym "S" [_] <- v -> Just (b, "collapseSgnSucc")
      _ -> Nothing
    predSteps t = case [u | u@(CSym "prd" [CSym "S" [_]]) <- subterms t] of
      u@(CSym "prd" [CSym "S" [x]]) : _ -> let t' = replaceCT (\y -> if y == u then Just x else Nothing) t in (t', "prd_S") : predSteps t'
      _ -> []

    -- The code of a tuple taken apart, step by step: tl, and hd, of a cons, with the lemma rewriting it.
    takeApart t = case redexOf t of
      Just (u, u', lem) -> let t' = replaceCT (\x -> if x == u then Just u' else Nothing) t in (t', lem) : takeApart t'
      Nothing -> []
    redexOf t = case t of
      CSym "tl" [CSym "cons" [_, b]] -> Just (t, b, "tlCons")
      CSym "hd" [CSym "cons" [a, _]] -> Just (t, a, "hdCons")
      CSym _ xs -> listToMaybe (mapMaybe redexOf xs)
      _ -> Nothing
    untuple = \case
      CSym "cons" [x, rest'] -> x : untuple rest'
      _ -> []
    subterms t =
      t : case t of
        CSym _ xs -> concatMap subterms xs
        _ -> []

    forM_' xs f = mapM_ f xs
    isVar = \case
      PVar _ -> True
      PWild -> True
      PAbsurd -> True
      _ -> False
    position xs i = length (takeWhile (/= i) xs)
    lastOf d = \case
      [] -> d
      xs -> snd (last xs)
    -- Each step of a chain of rewrites, starting from a term.
    scanl1' rewrites t0 = drop 1 (scanl (\(_, t) (j, f) -> (j, f t)) (0, t0) rewrites)
    argsWith c x rest = let (before, after) = splitAt c rest in before <> [x] <> after
    -- The definition, over the parameters of its schema, in braces, and its arguments.
    definition b =
      runBuilder
        ( unwordsB (fromText core : ["{" <> intercalateB ", " [fromText (staticName j) | j <- [1 .. length statics]] <> "}" | not (null statics)] <> map (fromText . argName) [0 .. arity - 1])
            <> " = "
            <> render b
        )
    equation lhs rhs = "(" <> render lhs <> " = " <> render rhs <> ")"
    -- A lemma: a theorem, or, for a function under constraints, a rule over the parameters of its schema, its variables all term metavariables.
    lemma name vs lhs rhs proof
      | null statics = runBuilder ("theorem " <> fromText name <> " : |- " <> equation lhs rhs <> "\nby " <> proof)
      | otherwise = runBuilder ("rule " <> fromText name <> ruleBinders [(staticName j, slotArity s) | (j, s) <- zip [1 :: Int ..] statics] (nub (concatMap varsCT vs)) <> " : |- " <> equation lhs rhs <> "\nby " <> proof)
    calc lhs steps = "calc " <> render lhs <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps]
    unfoldings triples =
      concat
        [ [ (functionLemma info n, lemma (functionLemma info n) [lhs] lhs rhs proof)
          , (functionLemma info alias, lemma (functionLemma info alias) [lhs] lhs rhs ("exact " <> fromText (functionLemma info n)))
          ]
        | (i, n, (lhs, rhs, proof)) <- zip3 [1 :: Int ..] names triples
        , let alias = "eq_" <> T.pack (show i)
        ]

    -- The clause's variables as core variables, by their names.
    varOf fc i = CVar (mangleVariable (fst (fcVars fc !! i)))
    argVar ps fc i = case [j | (j, Arg a) <- zip [0 ..] ps, a == i] of
      j : _ -> varOf fc j
      []
        | i >= userArity -> CVar (valueVar (T.pack (show (i - userArity))))
        | otherwise -> CVar ("v__x23_" <> T.pack (show i))
    fieldVars ps fc ci = [maybe (CVar ("v__x23_f" <> T.pack (show j))) (varOf fc) (lookup (Field j) (zip ps [0 ..])) | j <- [0 .. length (ctorFields ci) - 1]]
    patternArgs ps fc = [patternArg ps fc i p | (i, p) <- zip [0 ..] (fcPatterns fc)]
    patternArg ps fc i = \case
      PCon (Ref _ r) _ -> maybe (CVar "?") (\ci -> CSym (ctorCore ci) (fieldVars ps fc ci)) (ctorByCore env r)
      PNat n -> CNum n
      PSucc _ -> CSym "S" [natFieldVar ps fc]
      _ -> argVar ps fc i
    -- The predecessor a successor pattern binds, or a variable of its own.
    natFieldVar ps fc = maybe (CVar "v__x23_f0") (varOf fc) (lookup (Field 0) (zip ps [0 ..]))
    clauseRhs ps fc = body (varOf fc) inLemma (\callArgs -> Right (CSym core (map snd callArgs <> dict))) fc <* pure ps
    table triples = [(functionLemma info n, lhs, rhs) | (n, (lhs, rhs, _)) <- zip names triples]
    argIndex ps i = case ps !! i of
      Arg a -> a
      Field _ -> 0
    placeCT scr other ps i = case ps !! i of
      Arg a -> other a
      Field j -> fieldT j scr
    branchAt scr ps fc = either (error "internal") id (body (placeCT scr (argVar ps fc) ps) inLemma (const (Left "")) fc)
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
    recursiveFields ps fc = mapMaybe (\case (Field j, True) -> Just j; _ -> Nothing) [(p, i `elem` recVars core fc) | (i, p) <- zip [0 ..] ps]
    -- A recursive call: on a field of the scrutinee, the function's other arguments unchanged.
    recursiveCall c userOthers ps _fc k h callArgs = do
      unless (length callArgs == length userOthers + 1) $
        Left ("a recursive call with " <> show (length callArgs) <> " arguments, where the function takes " <> show (length userOthers + 1))
      field <- case fst (callArgs !! c) of
        Just i | Field j <- ps !! i -> Right j
        _ -> Left "a recursive call must pass a field of the matched constructor where the function matches"
      forM_' [(i, a) | (i, (a, _)) <- zip [0 ..] callArgs, i /= c] \(i, a) -> case (a, [j | (j, Arg x) <- zip [0 ..] ps, x == i]) of
        (Just v, [j]) | v == j -> Right ()
        _ -> Left "a recursive call must pass the other arguments unchanged (primitive recursion)"
      -- The field of a value of Nat is its predecessor.
      Right (CSym "at" [h, k, if fdArgs fd !! c == TNat then CSym "prd" [k] else fieldT field k])

{- |
The binders of a rule over the parameters of a schema, by their names and
arities — the places of a dictionary taking arguments, abstract functions —
and over the variables given, as term metavariables: a lemma with
metavariables has no free variables of its own.
-}
ruleBinders :: [(Text, Int)] -> [Text] -> Builder
ruleBinders statics vs =
  (if null zs then "" else " (" <> unwordsB (map fromText zs) <> " : var)")
    <> mconcat [" (" <> fromText n <> "(" <> intercalateB ", " (map fromText (take a zs)) <> ") : term)" | (n, a) <- statics]
    <> (if null vs then "" else " (" <> unwordsB (map fromText vs) <> " : term)")
  where
    zs = ["z_" <> T.pack (show i) | i <- [1 .. maximum (0 : map snd statics)]]

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
The core term of a clause's body: the variables by the first function given,
the values of the dictionary by the second, the recursive calls by the third,
their own arguments already translated.  A recursive call passes the
dictionary on unchanged, as primitive recursion keeps the parameters of a
schema.  A parameter of the dictionary, applied, is the parameter of the
schema applied; passed on, the parameter in braces.
-}
bodyCT :: FunInfo -> Int -> (Int -> CT) -> (Int -> CT) -> ([(Maybe Int, CT)] -> Either String CT) -> FunClause -> Either String CT
bodyCT info userArity var dvar rec fc = go (fromScope (fcBody fc))
  where
    core = funCore info
    own = ownDictionary (funSlots info)
    go e = case spine e of
      (Var (B i), []) -> Right (var i)
      (Var (F v), _) -> absurd v
      (Global (Ref RefStatic w), []) -> Right (CStatic w)
      (Global (Ref RefStatic w), as) -> CSym w <$> traverse go as
      (Global (Ref (RefPartial n) f), dict) -> (\d -> CPartial f d n) <$> traverse go dict
      (Global (Ref RefValueParam k), []) -> dvar <$> maybe (Left "internal: a value of the dictionary at no position") Right (readMaybe (T.unpack k))
      (Global (Ref _ r), as)
        | r == core -> do
            let (users, passed) = splitAt userArity (dropProofs as)
            unless (map stripLocations passed == own) $
              Left "a recursive call passes the dictionary on unchanged: primitive recursion keeps the parameters of its schema"
            cts <- traverse go users
            rec (zip (map variable users) cts)
        | otherwise -> CSym r <$> traverse go (dropProofs as)
      -- A proof given for what cannot be, absurd p: a value of any type, 0.
      (ProofArg {}, _) -> Right (CNum 0)
      (Nat n, []) -> Right (CNum n)
      _ -> Left "no core term for this expression"
    -- The pattern variable an argument is, when it is one.
    variable a = case stripLocations a of
      Var (B i) -> Just i
      _ -> Nothing
