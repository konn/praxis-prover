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
  paramName,

  -- * Equations of indices
  ctorIndexEquations,
  positionVar,
  atPositions,

  -- * Names of the generated lemmas
  ctorLemma,
  dataLemma,
  collapseLemma,
  membershipBody,
  membershipLambda,
) where

import Data.List (nub, sort)
import Data.Maybe (catMaybes, listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal)
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
are those the function given knows, by its qualified name: an index of a type
whose index functions it does not know, one encoded later, is not checked.
-}
ctorIndexEquations :: (Text -> Maybe [Text]) -> CtorInfo -> [(CT, CT)]
ctorIndexEquations indexFns c = case ctorGadt c of
  Nothing -> []
  Just g ->
    let tele = gcTele g
        -- The term an entry is, over the code.
        entry e = case teRole <$> listToMaybe (drop e tele) of
          Just (Explicit p) -> Just (positionVar p)
          Just (Stored p) -> Just (positionVar p)
          Just (Recovered p j) -> case drop p (ctorFields c) of
            TData dn _ _ : _ -> (\fn -> CSym fn [positionVar p]) <$> (indexFns dn >>= listToMaybe . drop j)
            _ -> Nothing
          Nothing -> Nothing
        index = \case
          IxParam i -> entry i
          IxNat n -> Just (CNum n)
          IxSucc x -> (\y -> CSym "S" [y]) <$> index x
          IxCon k xs -> CSym k <$> traverse index xs
          IxFun f xs -> CSym f <$> traverse index xs
          IxVar _ -> Nothing
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

-- | The equations of indices a constructor's branch checks, at a code: each as the code of its truth, @s == t@.
indexEquationCodes :: (CtorInfo -> [(CT, CT)]) -> CtorInfo -> CT -> [CT]
indexEquationCodes eqsOf c k = [CSym "eq" [atPositions (`fieldT` k) l, atPositions (`fieldT` k) r] | (l, r) <- eqsOf c]

-- | The core name of a lemma about a constructor: @C.#tag@, @C.#field-1@, …
ctorLemma :: CtorInfo -> Text -> Text
ctorLemma c suffix = mangleGlobal (map segmentRaw (ctorQual c) <> ["#" <> suffix])

-- | The core name of a lemma about a data type: @T.#inversion@, @T.#is-def@, …
dataLemma :: DataInfo -> Text -> Text
dataLemma d suffix = mangleGlobal (map segmentRaw (dataQual d) <> ["#" <> suffix])

-- | The lemma collapsing the dispatch of a data type at the tag given.
collapseLemma :: DataInfo -> Int -> Text
collapseLemma d i = dataLemma d ("collapse-" <> T.pack (show i))

var :: Int -> CT
var j = CVar ("v_" <> T.pack (show j))

{- |
The membership predicate's step, over @k@ and its history @h@: the dispatch
on the tag, each branch the exact shape, the memberships of the fields, and
the equations of indices given for the constructor.  The predicates of the
data types already encoded are given by name.
-}
membershipBody :: (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [(CT, CT)]) -> DataInfo -> CT -> CT -> CT
membershipBody = membershipBodyWith []

-- | 'membershipBody', the terms given after each field where its parameter's predicate is applied or passed on.
membershipBodyWith :: [CT] -> (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [(CT, CT)]) -> DataInfo -> CT -> CT -> CT
membershipBodyWith extras known eqsOf d k h = ifChain (hdT k) (map branch (dataCtors d))
  where
    branch c = case map snd (fieldMembershipsWith extras known d c k h) <> indexEquationCodes eqsOf c k of
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
membershipLambda :: (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [(CT, CT)]) -> DataInfo -> Text
membershipLambda = membershipLambdaWith []

-- | 'membershipLambda', the terms given after each field where its parameter's predicate is applied or passed on.
membershipLambdaWith :: [CT] -> (Text -> Maybe (Text, [Int])) -> (CtorInfo -> [(CT, CT)]) -> DataInfo -> Text
membershipLambdaWith extras known eqsOf d = runBuilder ("{λ k h. " <> render (membershipBodyWith extras known eqsOf d (CVar "k") (CVar "h")) <> "}")

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
encodeData known isVariadic indexFns d = Encoded codes codeLemmas predicate predicateLemmas members indexEquations params variadic
  where
    ctors = dataCtors d
    isCore = dataIs d
    params = predicateParams known d
    fieldsOf = [fieldPreds known d params c | c <- ctors]
    eqsOf = ctorIndexEquations indexFns
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
    lam = membershipLambda known eqsOf d
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
              <> if null ctors then "0" else "cvrec " <> fromText (if variadic then membershipLambdaWith [CVar "$[ys]"] known eqsOf d else lam) <> " n"
          )
      ]

    codeLemmas = concatMap ctorLemmas ctors <> collapses
    predicateLemmas = membership <> map intro ctors <> [inversion]
    members = [(ctorCore c, fieldPreds known d params c) | c <- ctors]
    indexEquations = [(ctorCore c, eqsOf c) | c <- ctors]

    {- The memberships of its fields, and the equations of indices of its
    entries |- 0 < T.is (C x̄): the code of every value is a member, the
    premise of the adequacy of statements.  The predicate unfolds at the code
    to the branch of C, whose shape conjunct is eqRefl once the fields are
    rewritten to the variables, whose membership conjuncts are the
    hypotheses, through the history for the fields of T itself, and whose
    equations are the hypotheses once the fields are rewritten. -}
    intro c =
      let k = length (ctorFields c)
          vs = map var [0 .. k - 1]
          applied = CSym (ctorCore c) vs
          h = histAt' applied
          mems = fieldMemberships known d c applied h
          eqs = eqsOf c
          dispatch = membershipBody known eqsOf d applied h
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
          -- An equation of indices: its conjunct, the fields rewritten to the variables position by position, is its hypothesis's truth.
          equation idx (l, r) =
            let code0 = CSym "eq" [atPositions (`fieldT` applied) l, atPositions (`fieldT` applied) r]
                ps = positions (CSym "eq" [l, r])
                steps = scanl (\s p -> replaceCT (\u -> if u == fieldT p applied then Just (vs !! p) else Nothing) s) code0 ps
             in "have M"
                  <> show' idx
                  <> ": ("
                  <> lt0 code0
                  <> " = 1) { calc "
                  <> lt0 code0
                  <> mconcat [" = " <> lt0 s <> " by cong " <> fieldLemma' p | (p, s) <- zip ps (drop 1 steps)]
                  <> " = 1 by exact eqIntro on H"
                  <> show' idx
                  <> " }; "
          codes' = map snd mems <> indexEquationCodes eqsOf c applied
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
              ([lt0eq1 (onField code (vs !! j)) | (j, code) <- mems] <> [eqn (atPositions (vs !!) l) (atPositions (vs !!) r) | (l, r) <- eqs])
              (lt0eq1 isApplied)
              (unfold <> shape <> mconcat (zipWith member [1 ..] mems) <> mconcat (zipWith equation [length mems + 1 ..] eqs) <> conclude)
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
          [ (dataLemma d "is-def", lemma (dataLemma d "is-def") [n] [] (eqn (isAt n) (cvrecAt n)) "refl")
          , (dataLemma d "is-beta", lemma (dataLemma d "is-beta") [n] [] (eqn (cvrecAt n) (membershipBody known eqsOf d n (histAt' n))) "refl")
          ]

    -- 0 < T.is t |- the disjunction of the shapes t may have, with the memberships of their fields and the equations of their indices.
    inversion = (dataLemma d "inversion", lemma (dataLemma d "inversion") [t] [lt0eq1 (isAt t)] (disjunction (map disjunct ctors)) script)
    disjunct c =
      let fs = [fieldT j t | j <- [0 .. length (ctorFields c) - 1]]
          eqT = "(" <> render t <> " = " <> render (CSym (ctorCore c) fs) <> ")"
          mems = [lt0eq1 (onField m (fieldT j t)) | (j, m) <- fieldMemberships known d c t (histAt' t)]
          eqs = [eqn l r | (l, r) <- indexEquationsAt c t]
       in conjunction (eqT : mems <> eqs)
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

    body = membershipBody known eqsOf d t (histAt' t)
    rest i = foldr (\(j, b) acc -> CSym "ifte" [CSym "eq" [hdT t, CNum j], b, acc]) (CNum 0) (drop i (zip [0 ..] (branches t)))
    branches x = [branchOf c x | c <- ctors]
    branchOf c x = case membershipBody known eqsOf d x (histAt' x) of
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
    -- From 0 < the branch of c: the equation, the memberships and the equations of indices, then the disjunct of c.
    extract c br =
      let mems = fieldMemberships known d c t (histAt' t)
          eqs = indexEquationsAt c t
          codes' = map snd mems <> [CSym "eq" [l, r] | (l, r) <- eqs]
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
          memProofs = mconcat (zipWith memProof [1 :: Int ..] mems) <> mconcat (zipWith eqProof [length mems + 1 ..] eqs)
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
