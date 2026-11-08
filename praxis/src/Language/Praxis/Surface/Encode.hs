{-# LANGUAGE OverloadedStrings #-}

{- |
Data types as tagged finite sequences, and the lemmas about them the
generated proofs appeal to.

A constructor @Cᵢ@, the @i@-th of its type from 0, with fields @x₁ … xₖ@ is
the code @⟨i, x₁, …, xₖ⟩ = cons i (cons x₁ … (cons xₖ 0))@, a definition of
its own in the core so that goals show its name.  Its tag is @hd c@ and its
field @j@ is @hd (tl^(j+1) c)@, with the prelude's @hd@ and @tl@.  Distinct
constructors have distinct tags, @cons@ is injective, and each field is
below the code: what structural recursion and induction need.

The membership predicate @T.is@ recognises the codes of @T@ by
course-of-values recursion: the tag is in range, the code is exactly the
constructor applied to its fields (no junk), and every field of @T@ itself,
or of a data type declared before, is a member in turn.  Fields of a type
parameter, of a higher-kinded parameter, of @Nat@ or of a type declared later
are not constrained, which only weakens the hypotheses a statement gets.

A constructor of a data type in the GADT style builds a value of its type at
the indices of its result only from entries at the indices its signature
gives them: the predicate also checks, for each entry of its telescope of an
indexed type, the equations of that type's indices at the entry
('ctorIndexEquations').  It is therefore defined after the index functions,
which come after the codes: 'encodedCodes', with the lemmas about them, then
the index functions, then 'encodedPredicate', with the lemmas about it.
After those equations it checks the constructor's preconditions, the
propositions of its proofs, which its code does not store, each by its code
('ctorPropositions'): a proposition every quantifier of which is bounded is
decided by a primitive recursive function of its terms, and the core's
@reify@ and @reflect@ pass between it and the truth of its code.  The
introduction takes the proposition as a hypothesis, and the inversion gives
it back, so that a clause's pattern may name the proof as a hypothesis.

The lemmas about the predicate are its unfolding, the introduction of each
constructor, @C.#intro@, the inversion, @T.#inversion@, and the induction
principle, @T.#induction@: a rule over an abstract function @q@ of the code,
the motive, with a premise for each constructor over its fields as variables
of its own, under their memberships, the equations of their indices and the
induction hypotheses, @0 < q(x)@ at each field of @T@ itself, concluding @0
< T.is t, Γ |- 0 < q(t)@.  It is proved once, by course-of-values induction
on @imp (T.is n) (q n)@ with the inversion, and every induction on a value of
@T@ the proof engine assembles appeals to it ("Language.Praxis.Surface.Engine").

Every lemma is generated as a declaration of the core, in its concrete
syntax, and certified by the core like any other; see
"Language.Praxis.Surface.CoreText" for how the text is built.  Definitional
equality is used on statements over variables only, and instantiated by
lemma appeals, never on the codes of constructors themselves, whose
normalisation does not terminate in reasonable time.
-}
module Language.Praxis.Surface.Encode (
  Encoded (..),
  FieldPred (..),
  ParamPred (..),
  encodeData,
  validateEncoding,
  paramName,

  -- * Equations of indices and preconditions
  ctorIndexEquations,
  ctorPropositions,
  position,
  positionVar,
  atPositions,
  propositionAt,

  -- * Names of the generated lemmas
  ctorLemma,
  dataLemma,
  collapseLemma,
  natInductionLemma,
  inductionLocal,
  membershipBody,
  membershipLambda,
) where

import Bound (Var (..), fromScope)
import Control.Monad (forM_, unless, when)
import Data.List (nub, sort)
import Data.Maybe (catMaybes, listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Data.Void (absurd)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Syntax qualified as S
import Language.Praxis.Surface.Syntax.Raw (segmentRaw)
import Language.Praxis.Surface.Types (Ix (..), Kind (..), Ty (..), normIx)
import Text.Read (readMaybe)

-- | What a data type is in the core: its definitions, and its lemmas with their declarations, in order.
data Encoded = Encoded
  { encodedCodes :: ![Text]
  -- ^ the definitions of its constructors' codes
  , encodedCodeLemmas :: ![(Text, Text)]
  -- ^ the lemmas about the codes: each constructor's, and the dispatch on the tag collapsed at each tag
  , encodedPredicate :: ![Text]
  -- ^ the definition of its membership predicate, which comes after its index functions
  , encodedLemmas :: ![(Text, Text)]
  -- ^ the lemmas about the predicate: its unfolding, each constructor's introduction, and the inversion
  , encodedMembers :: ![(Text, [(Int, FieldPred)])]
  -- ^ for each constructor, by its core name, the fields whose membership its branch of the predicate checks, with their predicates
  , encodedIndexEquations :: ![(Text, [(CT, CT)])]
  -- ^ for each constructor, by its core name, the equations of indices its branch checks after those, over the positions of its code
  , encodedProps :: ![(Text, [S.Expr Text])]
  -- ^ for each constructor, by its core name, its preconditions, which its branch checks after the equations of indices: the propositions of its proofs, over the positions of its code
  , encodedParams :: ![Int]
  -- ^ the parameters of the type whose predicates its own takes, those its fields' memberships use
  , encodedVariadic :: !Bool
  -- ^ whether its predicate is a variadic template, taking the terms its parameter's predicate captures
  }

{- |
The membership a field of a constructor has: by the predicate of a parameter
of its type, or by a data type's predicate, its own or one encoded before, at
predicates of those parameters in turn.
-}
data FieldPred = FieldParam !Int | FieldData !Text ![ParamPred]
  deriving stock (Show, Eq)

-- | A predicate standing as the parameter of a data type's: a parameter's own, every code's, or a data type's at predicates in turn.
data ParamPred = ParamOf !Int | ParamAny | ParamData !Text ![ParamPred]
  deriving stock (Show, Eq)

-- | The parameter of a data type's predicate standing for the predicate of the type's parameter at that index.
paramName :: Int -> Text
paramName i = "p" <> T.pack (show i)

-- | The parameters of a data type of kind @Type@, which a predicate may be given for.
firstOrderParams :: DataInfo -> [Int]
firstOrderParams d = [i | (i, (_, KType)) <- zip [0 ..] (dataParams d)]

{- |
The memberships of a constructor's fields, by their predicates: a field of a
parameter by the parameter's predicate; a field of the type itself, at its
own parameters, by the type's own predicate, at the parameters given; a
field of a data type encoded before, by its predicate at the predicates of
its arguments.  A field of @Nat@, of a higher-kinded parameter, of a type
encoded later, or of the type itself at other arguments, is not constrained.
-}
fieldPreds :: (Text -> Maybe (Text, [Int])) -> DataInfo -> [Int] -> CtorInfo -> [(Int, FieldPred)]
fieldPreds known d own c = catMaybes (zipWith one [0 ..] (ctorFields c))
  where
    self = renderQualName (dataQual d)
    fo = firstOrderParams d
    uniform = [TParam i [] | i <- [0 .. length (dataParams d) - 1]]
    one j = \case
      TParam i [] | i `elem` fo -> Just (j, FieldParam i)
      TData n targs _
        | n == self, targs == uniform -> Just (j, FieldData (dataIs d) (map ParamOf own))
        | n /= self, Just (p, used) <- known n -> Just (j, FieldData p [param (targs !! u) | u <- used, u < length targs])
      _ -> Nothing
    param = \case
      TParam i [] | i `elem` fo -> ParamOf i
      TData n targs _ | n /= self, Just (p, used) <- known n -> ParamData p [param (targs !! u) | u <- used, u < length targs]
      _ -> ParamAny

-- | The parameters a data type's predicate takes: those its fields' memberships use, in order.
predicateParams :: (Text -> Maybe (Text, [Int])) -> DataInfo -> [Int]
predicateParams known d = sort (nub [i | c <- dataCtors d, (_, fp) <- fieldPreds known d [] c, i <- ofField fp])
  where
    ofField = \case
      FieldParam i -> [i]
      FieldData _ ps -> concatMap ofParam ps
    ofParam = \case
      ParamOf i -> [i]
      ParamAny -> []
      ParamData _ ps -> concatMap ofParam ps

-- | A predicate standing as a parameter, as the core writes it.
paramCT :: ParamPred -> CT
paramCT = \case
  ParamOf i -> CStatic (paramName i)
  ParamAny -> CStatic "anyIs"
  ParamData p [] -> CStatic p
  ParamData p ps -> CPartial p (map paramCT ps) 1

{- |
A field's predicate applied to a term: the code whose truth is the term's
membership, the terms given after the term where the predicate of a
parameter is applied, or passed on as a parameter.
-}
fieldCodeWith :: [CT] -> FieldPred -> CT -> CT
fieldCodeWith extras fp x = case fp of
  FieldParam i -> CSym (paramName i) ([x] <> extras)
  FieldData p ps
    | any passed ps -> CSym p (map paramCT ps <> [x] <> extras)
    | otherwise -> CSym p (map paramCT ps <> [x])
  where
    passed = \case
      ParamOf _ -> True
      _ -> False

-- * Equations of indices

-- | A position of a constructor's code, as a variable of a term over the code: @#0@, @#1@, …, which no variable of the core is.
positionVar :: Int -> CT
positionVar p = CVar ("#" <> T.pack (show p))

-- | A term over the positions of a code, at the terms the function gives them.
atPositions :: (Int -> CT) -> CT -> CT
atPositions at = replaceCT \case
  CVar v | Just p <- position v -> Just (at p)
  _ -> Nothing

-- | The positions a term over a code mentions, in order.
positions :: CT -> [Int]
positions t = sort (nub (mapMaybe position (varsCT t)))

position :: Text -> Maybe Int
position v = T.stripPrefix "#" v >>= readMaybe . T.unpack

{- |
The equations of indices a constructor's code satisfies when the entries of
its telescope are at the indices its signature gives them: for each entry of
an indexed type, at each index of that type, the index function there
applied to the entry against the index the entry's type states, over the
positions of the code ('positionVar').  An entry is the field at its
position; an implicit argument the code does not store, the index of the
field it is recovered from, so that the equation it is recovered by is left
out, as every one which is so as it stands.  The index functions of a type
are those the function given knows, by its qualified name: unavailable index functions are rejected by 'validateEncoding' before
this encoding is admitted.
-}
ctorIndexEquations :: (Text -> Maybe [Text]) -> CtorInfo -> [(CT, CT)]
ctorIndexEquations indexFns c = case ctorSignature c of
  g ->
    let tele = constructorTele g
        entry = entryTerm indexFns c
        index = \case
          IxParam i -> entry i
          IxNat n -> Just (CNum n)
          IxSucc x -> (\y -> CSym "S" [y]) <$> index x
          IxCon k xs -> CSym k <$> traverse index xs
          IxFun f xs -> CSym f <$> traverse index xs
          IxSchema name -> Just (CStatic name)
          IxPartial name arity prefix xs -> (\captures -> CIndexedPartial name captures arity prefix) <$> traverse index xs
          IxLocal {} -> Nothing
          IxMeta {} -> Nothing
          IxFree _ -> Nothing
          IxDict _ -> Nothing
          IxMethod _ -> Nothing
          IxHole -> Nothing
     in [ (l, r)
        | (e, TeleEntry _ (TData dn _ ixs@(_ : _)) _) <- zip [0 ..] tele
        , Just fns <- [indexFns dn]
        , length fns == length ixs
        , Just at <- [entry e]
        , (fn, x) <- zip fns ixs
        , Just r <- [index (normIx x)]
        , let l = CSym fn [at]
        , l /= r
        ]

-- | The term an entry of a constructor's telescope is, over the positions of its code: a field or a stored implicit argument its position, a recovered one the index of a field.
entryTerm :: (Text -> Maybe [Text]) -> CtorInfo -> Int -> Maybe CT
entryTerm indexFns c e = case teRole <$> listToMaybe (drop e (constructorTele (ctorSignature c))) of
  Just (Explicit p) -> Just (positionVar p)
  Just (Stored p) -> Just (positionVar p)
  Just (Recovered p j) -> case drop p (ctorFields c) of
    TData dn _ _ : _ -> (\fn -> CSym fn [positionVar p]) <$> (indexFns dn >>= listToMaybe . drop j)
    _ -> Nothing
  Nothing -> Nothing

{- |
The preconditions of a constructor, the propositions of its proofs, over the
positions of its code, their terms the entries of its telescope as
'entryTerm' gives them; and the code of each ('propCode'), which the
membership predicate checks as it checks an equation of indices, after
those.  The introduction takes the proposition as a hypothesis and proves
the truth of its code, by the core's @reify@; the inversion gives the
proposition back from that truth, by @reflect@.  A proposition mentioning
an entry the code does not determine, or quantifying without a bound, has no
code, with why: 'validateEncoding' then refuses the encoding.
-}
ctorPropositions :: (Text -> Maybe [Text]) -> CtorInfo -> [Either String (S.Expr Text, CT)]
ctorPropositions indexFns c = [proposition p | (_, p) <- constructorProofs (ctorSignature c)]
  where
    entry e = maybe (S.Var "?") fromCT (entryTerm indexFns c e)
    proposition p = do
      let prop =
            fromScope p >>= \case
              B e -> entry e
              F v -> absurd v
      S.boundedProposition prop
      when ("?" `elem` prop) $ Left "it mentions an entry the code does not determine"
      code <- propCode CVar prop
      pure (prop, code)

-- | A proposition over the positions of a code, at the terms the function gives them, as 'atPositions' takes a term there.
propositionAt :: (Int -> CT) -> S.Expr Text -> S.Expr Text
propositionAt at prop = prop >>= \v -> maybe (S.Var v) (fromCT . at) (position v)

-- | The formula of a precondition, as the generated lemmas state it; one 'ctorPropositions' admitted always has one.
propositionText :: S.Expr Text -> Builder
propositionText prop = either (\why -> error ("internal: a precondition admitted has no formula: " <> why)) id (propText (\h -> "b_" <> mangleVariable h) CVar prop)

{- | Refuse an encoding which would silently omit a logical condition. A
missing membership predicate is an explicitly weaker representation; a
missing constructor precondition or index equation is never eliminable.
-}
validateEncoding :: (Text -> Maybe [Text]) -> DataInfo -> Either String ()
validateEncoding indexFns d = forM_ (dataCtors d) $ \c -> do
  let signature = ctorSignature c
      failure why = Left (T.unpack (displayQualName (ctorQual c)) <> ": " <> why)
      knownIndex = \case
        IxParam i -> maybe False (const True) (entryTerm indexFns c i)
        IxNat _ -> True
        IxSucc x -> knownIndex x
        IxCon _ xs -> all knownIndex xs
        IxFun _ xs -> all knownIndex xs
        IxSchema _ -> True
        IxPartial _ _ _ xs -> all knownIndex xs
        _ -> False
  forM_ (ctorPropositions indexFns c) $ \case
    Left why -> failure ("a proof field's proposition cannot be checked by the PRA membership predicate: " <> why)
    Right _ -> pure ()
  forM_ (zip [0 ..] (constructorTele signature)) $ \(i, entry) -> case teType entry of
    TData name _ indices@(_ : _) -> do
      unless (maybe False ((== length indices) . length) (indexFns name)) $
        failure "a field's index functions are unavailable to its PRA membership predicate"
      unless (maybe False (const True) (entryTerm indexFns c i) && all knownIndex indices) $
        failure "a field's indices are not determined by its numerical representation"
    _ -> pure ()

-- | The codes a constructor's branch checks after the memberships of its fields, at a code: those given over the positions of its code, at the fields of the code.
conjunctCodes :: (CtorInfo -> [CT]) -> CtorInfo -> CT -> [CT]
conjunctCodes codesOf c k = [atPositions (`fieldT` k) code | code <- codesOf c]

-- | The core name of a lemma about a constructor: @C.#tag@, @C.#field-1@, …
ctorLemma :: CtorInfo -> Text -> Text
ctorLemma c suffix = mangleGlobal (map segmentRaw (ctorQual c) <> ["#" <> suffix])

-- | The core name of a lemma about a data type: @T.#inversion@, @T.#is-def@, …
dataLemma :: DataInfo -> Text -> Text
dataLemma d suffix = mangleGlobal (map segmentRaw (dataQual d) <> ["#" <> suffix])

-- | The lemma collapsing the dispatch of a data type at the tag given.
collapseLemma :: DataInfo -> Int -> Text
collapseLemma d i = dataLemma d ("collapse-" <> T.pack (show i))

{- |
The induction principle of @Nat@, @Nat.#induction@, by the name a data type's
has: stated and proved in the prelude, @src-pra/prelude.pra@, in the shape
of a generated one, a premise for @0@ and one for the successor over a
variable of its own, 'inductionLocal' @0@, without the membership of the
value, which every code has.
-}
natInductionLemma :: Text
natInductionLemma = mangleGlobal ["Nat", "#induction"]

{- |
The variable of its own a premise of an induction principle has for the
field at a position, @v_0@, @v_1@, …: what an appeal to the principle leaves
the premise over, since no variable of a goal is named so — the core names of
a goal's variables are mangled surface names, @v_x@, or the engine's own,
@e_0@, @z_1@ — so that a proof of the premise can name them.
-}
inductionLocal :: Int -> Text
inductionLocal j = "v_" <> T.pack (show j)

inductionLocalVar :: Int -> CT
inductionLocalVar = CVar . inductionLocal

var :: Int -> CT
var j = CVar ("v_" <> T.pack (show j))

{- |
The membership predicate's step, over @k@ and its history @h@: the dispatch
on the tag, each branch the exact shape, the memberships of the fields, and
the codes given for the constructor over the positions of its code — the
equations of indices of its entries, then its preconditions.  The predicates
of the data types already encoded are given by name.
-}
membershipBody :: (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [CT]) -> DataInfo -> CT -> CT -> CT
membershipBody = membershipBodyWith []

-- | 'membershipBody', the terms given after each field where its parameter's predicate is applied or passed on.
membershipBodyWith :: [CT] -> (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [CT]) -> DataInfo -> CT -> CT -> CT
membershipBodyWith extras known codesOf d k h = ifChain (hdT k) (map branch (dataCtors d))
  where
    branch c = case map snd (fieldMembershipsWith extras known d c k h) <> conjunctCodes codesOf c k of
      [] -> shape c
      ms -> CSym "conj" [shape c, conjs ms]
    shape c = CSym "eq" [k, CSym (ctorCore c) [fieldT j k | j <- [0 .. length (ctorFields c) - 1]]]
    conjs = \case
      [m] -> m
      m : ms -> CSym "conj" [m, conjs ms]
      [] -> CNum 1

{- |
The memberships a constructor's fields contribute, in order: the field's
index and the code of its membership, a field of the type itself through the
history.
-}
fieldMemberships :: (Text -> Maybe (Text, [Int])) -> DataInfo -> CtorInfo -> CT -> CT -> [(Int, CT)]
fieldMemberships = fieldMembershipsWith []

-- | 'fieldMemberships', the terms given after each field where its parameter's predicate is applied or passed on.
fieldMembershipsWith :: [CT] -> (Text -> Maybe (Text, [Int])) -> DataInfo -> CtorInfo -> CT -> CT -> [(Int, CT)]
fieldMembershipsWith extras known d c k h = [(j, code j fp) | (j, fp) <- fieldPreds known d (predicateParams known d) c]
  where
    code j = \case
      FieldData p _ | p == dataIs d -> CSym "at" [h, k, fieldT j k]
      fp -> fieldCodeWith extras fp (fieldT j k)

-- | The step function of the membership predicate, as a schema parameter.
membershipLambda :: (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [CT]) -> DataInfo -> Text
membershipLambda = membershipLambdaWith []

-- | 'membershipLambda', the terms given after each field where its parameter's predicate is applied or passed on.
membershipLambdaWith :: [CT] -> (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [CT]) -> DataInfo -> Text
membershipLambdaWith extras known codesOf d = runBuilder ("{λ k h. " <> render (membershipBodyWith extras known codesOf d (CVar "k") (CVar "h")) <> "}")

{- |
The definitions and lemmas of a data type, given the membership predicates
of the data types encoded before it, with the parameters each takes, and the
index functions of the data types, by their qualified names, whose indices
its predicate checks ('ctorIndexEquations').  The type's own predicate takes
the predicates of the parameters its fields' memberships use, @T.is {p0} n@,
and its lemmas are then rules over them.

A predicate of one parameter, which some field is of and which every other
field passes on only to a variadic predicate of one parameter in turn, is a
variadic template, @T.is {p0} n $[ys]@: at a predicate capturing terms, a
closure, it takes those terms and passes them on to the closure and to the
predicates it passes it to.  With none it is the plain predicate, so its
lemmas, stated there as rules over the parameter, hold at every closure.
-}
encodeData :: (Text -> Maybe (Text, [Int])) -> (Text -> Bool) -> (Text -> Maybe [Text]) -> DataInfo -> Encoded
encodeData known isVariadic indexFns d = Encoded codes codeLemmas predicate predicateLemmas members indexEquations propositions params variadic
  where
    ctors = dataCtors d
    isCore = dataIs d
    params = predicateParams known d
    fieldsOf = [fieldPreds known d params c | c <- ctors]
    -- The equations of indices of a constructor's entries, and its preconditions with their codes, over the positions of its code.
    eqsOf c = ctorIndexEquations indexFns c
    propsOf c = [p | Right p <- ctorPropositions indexFns c]
    -- The codes a constructor's branch checks after the memberships: each equation of indices as the code of its truth, then the codes of its preconditions.
    codesOf c = [CSym "eq" [l, r] | (l, r) <- eqsOf c] <> map snd (propsOf c)
    propositions = [(ctorCore c, map fst (propsOf c)) | c <- ctors]
    variadic = case params of
      [i] -> any (any ((== FieldParam i) . snd)) fieldsOf && all (all (passes i . snd)) fieldsOf
      _ -> False
    -- A field's membership passes the parameter's predicate on where it can take what a closure captures.
    passes i = \case
      FieldParam _ -> True
      FieldData q ps
        | q == isCore -> True
        | ps == [ParamOf i] -> isVariadic q
        | otherwise -> not (any uses ps)
    uses = \case
      ParamOf _ -> True
      ParamAny -> False
      ParamData _ ps -> any uses ps
    -- The predicate at its parameters, applied: the code whose truth is the membership of x.
    isAt x = CSym isCore ([CStatic (paramName i) | i <- params] <> [x])
    paramsHead = if null params then "" else " {" <> intercalateB ", " (map (fromText . paramName) params) <> "}"
    -- A membership code at another term: through the history, the type's own predicate there; any other, its predicate applied there.
    onField code v = case code of
      CSym "at" _ -> isAt v
      CSym p as@(_ : _) -> CSym p (take (length as - 1) as <> [v])
      other -> other
    lt0eq1 x = "((lt 0 " <> render x <> ") = 1)"
    -- A lemma about the predicate: a theorem, or, when it takes parameters, a rule over them, its variables term metavariables.
    lemma name vars hyps statement proof
      | null params = theorem name hyps statement proof
      | otherwise =
          let vs = nub (concatMap varsCT vars)
           in runBuilder
                ( "rule "
                    <> fromText name
                    <> " (z_1 : var)"
                    <> mconcat [" (" <> fromText (paramName i) <> "(z_1) : term)" | i <- params]
                    <> (if null vs then "" else " (" <> unwordsB (map fromText vs) <> " : term)")
                    <> " : "
                    <> intercalateB ", " hyps
                    <> " |- "
                    <> statement
                    <> "\nby "
                    <> proof
                )
    lam = membershipLambda known codesOf d
    -- An equation's left side is the name and its arguments, unparenthesised.
    codes =
      [ runBuilder (unwordsB (map fromText (ctorCore c : fields)) <> " = " <> render (consSeq (toInteger (ctorIndex c)) (map CVar fields)))
      | c <- ctors
      , let fields = ["a" <> T.pack (show j) | j <- [0 .. length (ctorFields c) - 1]]
      ]
    predicate =
      [ runBuilder
          ( fromText isCore
              <> paramsHead
              <> (if variadic then " n $[ys] = " else " n = ")
              <> if null ctors then "0" else "cvrec " <> fromText (if variadic then membershipLambdaWith [CVar "$[ys]"] known codesOf d else lam) <> " n"
          )
      ]

    codeLemmas = concatMap ctorLemmas ctors <> collapses
    predicateLemmas = membership <> map intro ctors <> [inversion, induction]
    members = [(ctorCore c, fieldPreds known d params c) | c <- ctors]
    indexEquations = [(ctorCore c, eqsOf c) | c <- ctors]

    {- The memberships of its fields, the equations of indices of its
    entries, and its preconditions |- 0 < T.is (C x̄): the code of every
    value is a member, the premise of the adequacy of statements.  The
    predicate unfolds at the code to the branch of C, whose shape conjunct is
    eqRefl once the fields are rewritten to the variables, whose membership
    conjuncts are the hypotheses, through the history for the fields of T
    itself, and whose equations and preconditions are the truths of the
    hypotheses once the fields are rewritten. -}
    intro c =
      let k = length (ctorFields c)
          vs = map var [0 .. k - 1]
          applied = CSym (ctorCore c) vs
          h = histAt' applied
          mems = fieldMemberships known d c applied h
          eqs = eqsOf c
          props = propsOf c
          dispatch = membershipBody known codesOf d applied h
          tagged = replaceCT (\u -> if u == hdT applied then Just (CNum (fromIntegral (ctorIndex c))) else Nothing) dispatch
          br = nth (ctorIndex c) dispatch
          shapeCode = CSym "eq" [applied, CSym (ctorCore c) [fieldT j applied | j <- [0 .. k - 1]]]
          -- the shape, its fields rewritten to the variables one by one
          shapes = scanl (\s j -> replaceCT (\u -> if u == fieldT j applied then Just (vs !! j) else Nothing) s) shapeCode [0 .. k - 1]
          isApplied = isAt applied
          name = ctorLemma c "intro"
          fieldLemma' j = fromText (ctorLemma c ("field-" <> T.pack (show j)))
          lt0 x = "(lt 0 " <> render x <> ")"
          unfold =
            "have W: ("
              <> render isApplied
              <> " = "
              <> render br
              <> ") { calc "
              <> render isApplied
              <> " = "
              <> render (cvrecAt applied)
              <> " by exact "
              <> fromText (dataLemma d "is-def")
              <> " = "
              <> render dispatch
              <> " by exact "
              <> fromText (dataLemma d "is-beta")
              <> " = "
              <> render tagged
              <> " by cong "
              <> fromText (ctorLemma c "tag")
              <> " = "
              <> render br
              <> " by exact "
              <> fromText (collapseLemma d (ctorIndex c))
              <> " }; "
          shape =
            "have Rf: ((eq "
              <> render applied
              <> " "
              <> render applied
              <> ") = 1) { exact eqRefl }; have Sh: ("
              <> lt0 shapeCode
              <> " = 1) { calc "
              <> lt0 shapeCode
              <> mconcat [" = " <> lt0 s <> " by cong " <> fieldLemma' j | (j, s) <- zip [0 ..] (drop 1 shapes)]
              <> " = (lt 0 1) by cong Rf = 1 }; "
          member idx (j, code) = case code of
            CSym "at" [hh, _, _] ->
              let atVar = CSym "at" [hh, applied, vs !! j]
               in "have L"
                    <> show' idx
                    <> ": "
                    <> ltT (vs !! j) applied
                    <> " { exact "
                    <> fromText (ctorLemma c ("lt-" <> T.pack (show j)))
                    <> " }; have A"
                    <> show' idx
                    <> ": ("
                    <> render atVar
                    <> " = "
                    <> render (cvrecAt (vs !! j))
                    <> ") { exact histAt }; have M"
                    <> show' idx
                    <> ": ("
                    <> lt0 code
                    <> " = 1) { calc "
                    <> lt0 code
                    <> " = "
                    <> lt0 atVar
                    <> " by cong "
                    <> fieldLemma' j
                    <> " = "
                    <> lt0 (cvrecAt (vs !! j))
                    <> " by cong A"
                    <> show' idx
                    <> " = "
                    <> lt0 (isAt (vs !! j))
                    <> " by cong "
                    <> fromText (dataLemma d "is-def")
                    <> " = 1 by exact H"
                    <> show' idx
                    <> " }; "
            CSym _ (_ : _) ->
              "have M"
                <> show' idx
                <> ": ("
                <> lt0 code
                <> " = 1) { calc "
                <> lt0 code
                <> " = "
                <> lt0 (onField code (vs !! j))
                <> " by cong "
                <> fieldLemma' j
                <> " = 1 by exact H"
                <> show' idx
                <> " }; "
            _ -> error "internal: a membership conjunct of another form"
          -- A conjunct checked after the memberships, its code at the fields: the fields rewritten to the variables position by position, then its truth at the variables by the proof given.
          conjunct idx code final =
            let code0 = atPositions (`fieldT` applied) code
                ps = positions code
                steps = scanl (\s p -> replaceCT (\u -> if u == fieldT p applied then Just (vs !! p) else Nothing) s) code0 ps
             in "have M"
                  <> show' idx
                  <> ": ("
                  <> lt0 code0
                  <> " = 1) { calc "
                  <> lt0 code0
                  <> mconcat [" = " <> lt0 s <> " by cong " <> fieldLemma' p | (p, s) <- zip ps (drop 1 steps)]
                  <> " = 1 by "
                  <> final
                  <> " }; "
          -- An equation of indices: the truth of its code is its hypothesis's, by eqIntro.
          equation idx (l, r) = conjunct idx (CSym "eq" [l, r]) ("exact eqIntro on H" <> show' idx)
          -- A precondition: the truth of its code from the hypothesis stating it, by reify where the code reads as the formula; where the hypothesis is that truth, as it stands.
          proposition idx (_, code) =
            conjunct idx code $
              if codeIsFormula code
                then "(reify H" <> show' idx <> " as R" <> show' idx <> "; exact R" <> show' idx <> ")"
                else "exact H" <> show' idx
          codes' = map snd mems <> conjunctCodes codesOf c applied
          conjs = \case
            [m] -> m
            m : ms -> CSym "conj" [m, conjs ms]
            [] -> CNum 1
          -- Q_i: 0 < the conjunction of the conjuncts from the i-th, innermost first.
          partial i =
            "have Q"
              <> show' i
              <> ": ("
              <> lt0 (conjs (drop (i - 1) codes'))
              <> " = 1) { exact "
              <> (if i == length codes' then "M" <> show' i else "conjIntro on M" <> show' i <> " Q" <> show' (i + 1))
              <> " }; "
          conclude =
            mconcat (map partial (reverse [1 .. length codes']))
              <> "have B: ("
              <> lt0 br
              <> " = 1) { exact "
              <> (if null codes' then "Sh" else "conjIntro on Sh Q1")
              <> " }; calc "
              <> lt0 isApplied
              <> " = "
              <> lt0 br
              <> " by cong W = 1 by exact B"
       in ( name
          , lemma
              name
              vs
              ([lt0eq1 (onField code (vs !! j)) | (j, code) <- mems] <> [eqn (atPositions (vs !!) l) (atPositions (vs !!) r) | (l, r) <- eqs] <> [propositionText (propositionAt (vs !!) prop) | (prop, _) <- props])
              (lt0eq1 isApplied)
              (unfold <> shape <> mconcat (zipWith member [1 ..] mems) <> mconcat (zipWith equation [length mems + 1 ..] eqs) <> mconcat (zipWith proposition [length mems + length eqs + 1 ..] props) <> conclude)
          )

    ctorLemmas c =
      let k = length (ctorFields c)
          vs = map var [0 .. k - 1]
          applied = CSym (ctorCore c) vs
          seqs = [consSeq' m | m <- [0 .. k + 1]]
          -- the sequence with its first m elements dropped
          consSeq' m = foldr (\x acc -> CSym "cons" [x, acc]) (CNum 0) (drop m (CNum (fromIntegral (ctorIndex c)) : vs))
          defName = ctorLemma c "def"
          haveE = "have E: (" <> render applied <> " = " <> render (seqs !! 0) <> ") { exact " <> fromText defName <> " }; "
          fieldLemma j =
            ( ctorLemma c ("field-" <> T.pack (show j))
            , theorem (ctorLemma c ("field-" <> T.pack (show j))) [] (eqn (fieldT j applied) (vs !! j)) $
                haveE
                  <> "calc "
                  <> render (fieldT j applied)
                  <> " = "
                  <> render (fieldT j (seqs !! 0))
                  <> " by cong E"
                  <> mconcat [" = " <> render (hdT (iterate tlT (seqs !! (m + 1)) !! (j - m))) <> " by cong tlCons" | m <- [0 .. j]]
                  <> " = "
                  <> render (vs !! j)
                  <> " by exact hdCons"
            )
          ltLemma j =
            ( ctorLemma c ("lt-" <> T.pack (show j))
            , theorem (ctorLemma c ("lt-" <> T.pack (show j))) [] (ltT (vs !! j) applied) $
                haveE
                  <> "have L"
                  <> show' (j + 1)
                  <> ": "
                  <> ltT (vs !! j) (seqs !! (j + 1))
                  <> " { exact ltConsL }; "
                  <> mconcat
                    [ "have R"
                        <> show' m
                        <> ": "
                        <> ltT (seqs !! (m + 1)) (seqs !! m)
                        <> " { exact ltConsR }; "
                        <> "have L"
                        <> show' m
                        <> ": "
                        <> ltT (vs !! j) (seqs !! m)
                        <> " { exact ltTrans on L"
                        <> show' (m + 1)
                        <> " R"
                        <> show' m
                        <> " }; "
                    | m <- reverse [0 .. j]
                    ]
                  <> "calc (lt "
                  <> render (vs !! j)
                  <> " "
                  <> render applied
                  <> ") = (lt "
                  <> render (vs !! j)
                  <> " "
                  <> render (seqs !! 0)
                  <> ") by cong E = 1 by exact L0"
            )
       in [ (defName, theorem defName [] (eqn applied (seqs !! 0)) "refl")
          , (ctorLemma c "tag", theorem (ctorLemma c "tag") [] (eqn (hdT applied) (CNum (fromIntegral (ctorIndex c)))) (haveE <> "calc " <> render (hdT applied) <> " = " <> render (hdT (seqs !! 0)) <> " by cong E = " <> show' (ctorIndex c) <> " by exact hdCons"))
          ]
            <> map fieldLemma [0 .. k - 1]
            <> map ltLemma [0 .. k - 1]

    -- The dispatch at tag i, at variables: its branch.
    collapses =
      [ (collapseLemma d i, theorem (collapseLemma d i) [] (eqn (ifChainAt i) (branchVar i)) "refl")
      | i <- [0 .. length ctors - 1]
      ]
    ifChainAt i = foldr (\(j, b) acc -> CSym "ifte" [CSym "eq" [CNum (fromIntegral i), CNum j], b, acc]) (CNum 0) (zip [0 ..] (map branchVar [0 .. length ctors - 1]))
    branchVar i = CVar ("v_b" <> T.pack (show i))

    n = CVar "v_n"
    t = CVar "v_t"
    cvrecAt x = CRaw (runBuilder ("cvrec " <> fromText lam <> " " <> render x))
    histAt' x = CRaw (runBuilder ("hist " <> fromText lam <> " " <> render x))
    membership
      | null ctors = []
      | otherwise =
          -- Reuse the checked schema: normalizing the whole instantiated
          -- predicate can exhaust conversion fuel for large GADTs.
          [ (dataLemma d "is-def", lemma (dataLemma d "is-def") [n] [] (eqn (isAt n) (cvrecAt n)) "refl")
          , (dataLemma d "is-beta", lemma (dataLemma d "is-beta") [n] [] (eqn (cvrecAt n) (membershipBody known codesOf d n (histAt' n))) "exact cvrecUnfold")
          ]

    -- 0 < T.is t |- the disjunction of the shapes t may have, with the memberships of their fields, the equations of their indices and their preconditions.
    inversion = (dataLemma d "inversion", lemma (dataLemma d "inversion") [t] [lt0eq1 (isAt t)] (disjunction (map (disjunctAt t) ctors)) script)
    -- The disjunct of a constructor at a code: the code is the constructor at its fields, which are members, and the equations of indices and the preconditions hold.
    disjunctAt x c =
      let fs = [fieldT j x | j <- [0 .. length (ctorFields c) - 1]]
          eqT = "(" <> render x <> " = " <> render (CSym (ctorCore c) fs) <> ")"
          mems = [lt0eq1 (onField m (fieldT j x)) | (j, m) <- fieldMemberships known d c x (histAt' x)]
          eqs = [eqn l r | (l, r) <- indexEquationsAt c x]
          props = [propositionText (propositionAt (`fieldT` x) prop) | (prop, _) <- propsOf c]
       in conjunction (eqT : mems <> eqs <> props)

    {- The induction principle, 0 < T.is t, Γ |- 0 < q(t) for an abstract
    function q of the code, the motive, with a premise for each constructor
    over its fields as variables of its own: under the memberships of the
    fields, the equations of indices and the preconditions the constructor's
    introduction takes, and the induction hypotheses, the motive at the
    fields of T itself, the motive holds at the constructor.  It is course-of-values induction,
    cvInduction, on imp (T.is n) (q n): in the step, the inversion splits the
    code on its constructors, and the induction hypothesis at a field is the
    instance in the history, belowElim, at the field's membership, the field
    being below the code (C.#lt-j). -}
    induction = (dataLemma d "induction", runBuilder inductionRule)
    cv = CVar "v_m"
    truthQ x = "((lt 0 (q" <> argQ x <> ")) = 1)"
    argQ x = case x of
      CSym _ (_ : _) -> render x
      _ -> "(" <> render x <> ")"
    -- The fields of the type itself, whose memberships the predicate checks through the history: those with induction hypotheses.
    recursiveFields c = [j | (j, FieldData p _) <- fieldPreds known d params c, p == isCore]
    premiseName c = "c_" <> fromDec (ctorIndex c)
    premiseOf c =
      let k = length (ctorFields c)
          vs = map inductionLocalVar [0 .. k - 1]
          applied = CSym (ctorCore c) vs
          facts =
            [lt0eq1 (onField code (vs !! j)) | (j, code) <- fieldMemberships known d c applied (histAt' applied)]
              <> [eqn (atPositions (vs !!) l) (atPositions (vs !!) r) | (l, r) <- eqsOf c]
              <> [propositionText (propositionAt (vs !!) prop) | (prop, _) <- propsOf c]
          ihs = [truthQ (vs !! j) | j <- recursiveFields c]
       in " ("
            <> premiseName c
            <> (if k == 0 then "" else " forall " <> unwordsB (map render vs))
            <> " : "
            <> intercalateB ", " (facts <> ihs <> ["Γ"])
            <> " |- "
            <> truthQ applied
            <> ")"
    inductionRule =
      "rule "
        <> fromText (dataLemma d "induction")
        <> " ("
        <> render t
        <> " : term) (z_1 : var)"
        <> mconcat [" (" <> fromText (paramName i) <> "(z_1) : term)" | i <- params]
        <> " (Γ : ctx) (q(z_1) : term)"
        <> mconcat (map premiseOf ctors)
        <> " : "
        <> lt0eq1 (isAt t)
        <> ", Γ |- "
        <> truthQ t
        <> "\nby "
        <> inductionProof
    inductionProof
      | null ctors = "have F: (_|_) { exact " <> fromText (dataLemma d "inversion") <> " on H1 }; ExFalso"
      | otherwise =
          "have C: ((lt 0 (imp "
            <> render (isAt t)
            <> " (q"
            <> argQ t
            <> "))) = 1) { exact cvInduction "
            <> render cv
            <> " "
            <> render t
            <> " { have Q: ("
            <> lt0eq1 (isAt cv)
            <> " ==> "
            <> truthQ cv
            <> ") { ImplR as M; have I: ("
            <> disjunction (map (disjunctAt cv) ctors)
            <> ") { exact "
            <> fromText (dataLemma d "inversion")
            <> " on M }; "
            <> splitDisj "I" (map inductionBranch ctors)
            <> " }; exact impIntro } }; exact impElim on C H1"
    -- The branches of the inversion, hypothesis by hypothesis.
    splitDisj h = \case
      [] -> "ExFalso"
      [b] -> b h
      b : bs -> "DisjL on " <> h <> " as " <> h <> "a " <> h <> "b { " <> b (h <> "a") <> " } { " <> splitDisj (h <> "b") bs <> " }"
    {- A branch, from its disjunct: the equation of the code, Km, then the
    memberships, the equations of indices and the preconditions, K1 … in
    order; the induction hypotheses of the fields of T; the premise at the
    fields; and the motive at the code by the equation. -}
    inductionBranch c h =
      let fs = [fieldT j cv | j <- [0 .. length (ctorFields c) - 1]]
          applied = CSym (ctorCore c) fs
          mems = fieldMemberships known d c cv (histAt' cv)
          conjuncts = length mems + length (eqsOf c) + length (propsOf c)
          splitConj = case conjuncts of
            0 -> "have Km: (" <> render cv <> " = " <> render applied <> ") { exact " <> h <> " }; "
            _ -> "ConjL on " <> h <> " as Km " <> conjNames conjuncts <> "; "
          conjNames nm = case nm of
            1 -> "K1"
            _ -> "Kr1; " <> mconcat ["ConjL on Kr" <> show' q <> " as K" <> show' q <> (if q + 1 == nm then " K" <> show' (q + 1) else " Kr" <> show' (q + 1)) <> "; " | q <- [1 .. nm - 1]] <> "skip"
          hypothesis j =
            let f = fs !! j
                kname = "K" <> show' (1 + length (takeWhile ((/= j) . fst) mems))
             in "have Lf"
                  <> show' j
                  <> ": "
                  <> ltT f applied
                  <> " { exact "
                  <> fromText (ctorLemma c ("lt-" <> T.pack (show j)))
                  <> " }; have Lm"
                  <> show' j
                  <> ": "
                  <> ltT f cv
                  <> " { calc (lt "
                  <> render f
                  <> " "
                  <> render cv
                  <> ") = (lt "
                  <> render f
                  <> " "
                  <> render applied
                  <> ") by cong Km = 1 by exact Lf"
                  <> show' j
                  <> " }; have IHc"
                  <> show' j
                  <> ": ((lt 0 (imp "
                  <> render (isAt f)
                  <> " (q"
                  <> argQ f
                  <> "))) = 1) { exact belowElim _ "
                  <> render cv
                  <> " "
                  <> render f
                  <> " }; have IHr"
                  <> show' j
                  <> ": "
                  <> truthQ f
                  <> " { exact impElim on IHc"
                  <> show' j
                  <> " "
                  <> kname
                  <> " }; "
       in splitConj
            <> mconcat (map hypothesis (recursiveFields c))
            <> "have A1: "
            <> truthQ applied
            <> " { exact "
            <> premiseName c
            <> " }; calc (lt 0 (q"
            <> argQ cv
            <> ")) = (lt 0 (q"
            <> argQ applied
            <> ")) by cong Km = 1 by exact A1"
    -- The equations of indices of a constructor, at the fields of a code.
    indexEquationsAt c x = [(atPositions (`fieldT` x) l, atPositions (`fieldT` x) r) | (l, r) <- eqsOf c]
    disjunction = \case
      [] -> "_|_"
      [x] -> x
      x : xs -> "(" <> x <> " \\/ " <> disjunction xs <> ")"
    conjunction = \case
      [x] -> x
      x : xs -> "(" <> x <> " /\\ " <> conjunction xs <> ")"
      [] -> "(0 = 0)"

    body = membershipBody known codesOf d t (histAt' t)
    rest i = foldr (\(j, b) acc -> CSym "ifte" [CSym "eq" [hdT t, CNum j], b, acc]) (CNum 0) (drop i (zip [0 ..] (branches t)))
    branches x = [branchOf c x | c <- ctors]
    branchOf c x = case membershipBody known codesOf d x (histAt' x) of
      b -> nth (ctorIndex c) b
    -- The branch of a dispatch at an index.
    nth i = \case
      CSym "ifte" [_, b, more] -> if i == 0 then b else nth (i - 1) more
      other -> other

    script
      | null ctors = "have V: (" <> render (isAt t) <> " = 0) { refl }; have W: ((lt 0 0) = 1) { calc (lt 0 0) = (lt 0 " <> render (isAt t) <> ") by cong V = 1 by exact H1 }; exact zeroPosAbsurd"
      | otherwise =
          "have V0: ("
            <> render (isAt t)
            <> " = "
            <> render body
            <> ") { calc "
            <> render (isAt t)
            <> " = "
            <> render (cvrecAt t)
            <> " by exact "
            <> fromText (dataLemma d "is-def")
            <> " = "
            <> render body
            <> " by exact "
            <> fromText (dataLemma d "is-beta")
            <> " }; "
            <> caseAt 0
    isT = render (isAt t)
    caseAt i
      | i == length ctors =
          "have W: ((lt 0 0) = 1) { calc (lt 0 0) = (lt 0 " <> isT <> ") by cong V" <> show' i <> " = 1 by exact H1 }; exact zeroPosAbsurd"
      | otherwise =
          let tagEq = render (CSym "eq" [hdT t, CNum (fromIntegral i)])
              br = branches t !! i
           in "have B"
                <> show' i
                <> ": (("
                <> tagEq
                <> ") = 0 \\/ ("
                <> tagEq
                <> ") = 1) { exact eqBool }; DisjL on B"
                <> show' i
                <> " as Z"
                <> show' i
                <> " O"
                <> show' i
                <> " { have V"
                <> show' (i + 1)
                <> ": ("
                <> isT
                <> " = "
                <> render (rest (i + 1))
                <> ") { calc "
                <> isT
                <> " = "
                <> render (rest i)
                <> " by exact V"
                <> show' i
                <> " = "
                <> render (CSym "ifte" [CNum 0, br, rest (i + 1)])
                <> " by cong Z"
                <> show' i
                <> " = "
                <> render (rest (i + 1))
                <> " by exact collapseF }; "
                <> caseAt (i + 1)
                <> " } { have W: ("
                <> isT
                <> " = "
                <> render br
                <> ") { calc "
                <> isT
                <> " = "
                <> render (rest i)
                <> " by exact V"
                <> show' i
                <> " = "
                <> render (CSym "ifte" [CNum 1, br, rest (i + 1)])
                <> " by cong O"
                <> show' i
                <> " = "
                <> render br
                <> " by exact collapseT }; "
                <> extract (ctors !! i) br
                <> " }"
    -- From 0 < the branch of c: the equation, the memberships, the equations of indices and the preconditions, then the disjunct of c.
    extract c br =
      let mems = fieldMemberships known d c t (histAt' t)
          eqs = indexEquationsAt c t
          props = propsOf c
          codes' = map snd mems <> conjunctCodes codesOf c t
          ctorApplied = CSym (ctorCore c) [fieldT j t | j <- [0 .. length (ctorFields c) - 1]]
          eqCode = CSym "eq" [t, ctorApplied]
          start = "have P: ((lt 0 " <> render br <> ") = 1) { calc (lt 0 " <> render br <> ") = (lt 0 " <> isT <> ") by cong W = 1 by exact H1 }; "
          splitEq = case codes' of
            [] -> "have E: (" <> render t <> " = " <> render ctorApplied <> ") { exact eqElim }; "
            _ ->
              "have Pe: ((lt 0 "
                <> render eqCode
                <> ") = 1) { exact conjElim1 on P }; have Pm: ((lt 0 "
                <> render (conjsOf codes')
                <> ") = 1) { exact conjElim2 on P }; have E: ("
                <> render t
                <> " = "
                <> render ctorApplied
                <> ") { exact eqElim on Pe }; "
          conjsOf = \case
            [m] -> m
            m : ms -> CSym "conj" [m, conjsOf ms]
            [] -> CNum 1
          -- K1 … the conjuncts' codes, from Pm by conjElim.
          memCodes = splitConj "Pm" codes' (1 :: Int)
          splitConj h ms idx = case ms of
            [] -> ""
            [m] -> "have K" <> show' idx <> ": ((lt 0 " <> render m <> ") = 1) { exact " <> h <> " }; "
            m : more ->
              "have K"
                <> show' idx
                <> ": ((lt 0 "
                <> render m
                <> ") = 1) { exact conjElim1 on "
                <> h
                <> " }; have J"
                <> show' idx
                <> ": ((lt 0 "
                <> render (conjsOf more)
                <> ") = 1) { exact conjElim2 on "
                <> h
                <> " }; "
                <> splitConj ("J" <> show' idx) more (idx + 1)
          memProofs = mconcat (zipWith memProof [1 :: Int ..] mems) <> mconcat (zipWith eqProof [length mems + 1 ..] eqs) <> mconcat (zipWith propProof [length mems + length eqs + 1 ..] props)
          memProof idx (j, code) = case code of
            CSym "at" [hh, _, f] ->
              "have Lf"
                <> show' idx
                <> ": "
                <> ltT f ctorApplied
                <> " { exact "
                <> fromText (ctorLemma c ("lt-" <> T.pack (show j)))
                <> " }; have Lt"
                <> show' idx
                <> ": "
                <> ltT f t
                <> " { calc (lt "
                <> render f
                <> " "
                <> render t
                <> ") = (lt "
                <> render f
                <> " "
                <> render ctorApplied
                <> ") by cong E = 1 by exact Lf"
                <> show' idx
                <> " }; have Ha"
                <> show' idx
                <> ": ("
                <> render (CSym "at" [hh, t, f])
                <> " = "
                <> render (cvrecAt f)
                <> ") { exact histAt }; have M"
                <> show' idx
                <> ": "
                <> lt0eq1 (isAt f)
                <> " { calc (lt 0 "
                <> render (isAt f)
                <> ") = (lt 0 "
                <> render (cvrecAt f)
                <> ") by cong "
                <> fromText (dataLemma d "is-def")
                <> " = (lt 0 "
                <> render (CSym "at" [hh, t, f])
                <> ") by cong Ha"
                <> show' idx
                <> " = 1 by exact K"
                <> show' idx
                <> " }; "
            _ -> "have M" <> show' idx <> ": " <> lt0eq1 code <> " { exact K" <> show' idx <> " }; "
          -- An equation of indices, from the truth of its code.
          eqProof idx (l, r) = "have M" <> show' idx <> ": " <> eqn l r <> " { exact eqElim on K" <> show' idx <> " }; "
          -- A precondition, from the truth of its code: the formula the code reads as, by reflect; or that truth as it stands.
          propProof idx (prop, code)
            | codeIsFormula code = "reflect K" <> show' idx <> " as M" <> show' idx <> "; "
            | otherwise = "have M" <> show' idx <> ": " <> propositionText (propositionAt (`fieldT` t) prop) <> " { exact K" <> show' idx <> " }; "
          conclude = case codes' of
            [] -> "exact E"
            _ -> conjR ("E" : ["M" <> show' idx | idx <- [1 .. length codes']])
          conjR = \case
            [x] -> "exact " <> x
            x : xs -> "ConjR { exact " <> x <> " } { " <> conjR xs <> " }"
            [] -> "skip"
          select = mconcat (replicate (ctorIndex c) "DisjR1; ") <> (if ctorIndex c < length ctors - 1 then "DisjR2; " else "")
       in start <> splitEq <> memCodes <> memProofs <> select <> conclude

    theorem name hyps statement proof = runBuilder ("theorem " <> fromText name <> " : " <> intercalateB ", " hyps <> " |- " <> statement <> "\nby " <> proof)
    eqn a b = "(" <> render a <> " = " <> render b <> ")"
    ltT a b = "((lt " <> render a <> " " <> render b <> ") = 1)"
    show' :: Int -> Builder
    show' = fromDec
