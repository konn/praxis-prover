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

Every lemma is generated as a declaration of the core, in its concrete
syntax, and certified by the core like any other; see
"Language.Praxis.Surface.CoreText" for how the text is built.  Definitional
equality is used on statements over variables only, and instantiated by
lemma appeals, never on the codes of constructors themselves, whose
normalisation does not terminate in reasonable time.
-}
module Language.Praxis.Surface.Encode (
  Encoded (..),
  encodeData,

  -- * Names of the generated lemmas
  ctorLemma,
  dataLemma,
  collapseLemma,
  membershipBody,
  membershipLambda,
) where

import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Syntax.Raw (Segment (..))
import Language.Praxis.Surface.Types (Ty (..))

-- | What a data type is in the core: its definitions, and its lemmas with their declarations, in order.
data Encoded = Encoded
  { encodedEquations :: ![Text]
  , encodedLemmas :: ![(Text, Text)]
  , encodedMembers :: ![(Text, [(Int, Text)])]
  -- ^ for each constructor, by its core name, the fields whose membership its branch of the predicate checks, with the predicate
  }

raw :: Segment -> Text
raw = \case
  Ident t -> t
  Op t -> t

-- | The core name of a lemma about a constructor: @C.#tag@, @C.#field-1@, …
ctorLemma :: CtorInfo -> Text -> Text
ctorLemma c suffix = mangleGlobal (map raw (ctorQual c) <> ["#" <> suffix])

-- | The core name of a lemma about a data type: @T.#inversion@, @T.#is-def@, …
dataLemma :: DataInfo -> Text -> Text
dataLemma d suffix = mangleGlobal (map raw (dataQual d) <> ["#" <> suffix])

-- | The lemma collapsing the dispatch of a data type at the tag given.
collapseLemma :: DataInfo -> Int -> Text
collapseLemma d i = dataLemma d ("collapse-" <> T.pack (show i))

var :: Int -> CT
var j = CVar ("v_" <> T.pack (show j))

{- |
The membership predicate's step, over @k@ and its history @h@: the dispatch
on the tag, each branch the exact shape and the memberships of the fields.
The predicates of the data types already encoded are given by name.
-}
membershipBody :: (Text -> Maybe Text) -> DataInfo -> CT -> CT -> CT
membershipBody known d k h = ifChain (hdT k) (map branch (dataCtors d))
  where
    branch c = case fieldMemberships known d c k h of
      [] -> shape c
      ms -> CSym "conj" [shape c, conjs (map snd ms)]
    shape c = CSym "eq" [k, CSym (ctorCore c) [fieldT j k | j <- [0 .. length (ctorFields c) - 1]]]
    conjs = \case
      [m] -> m
      m : ms -> CSym "conj" [m, conjs ms]
      [] -> CNum 1

-- | The memberships a constructor's fields contribute, in order: the field's index and the code of its membership.
fieldMemberships :: (Text -> Maybe Text) -> DataInfo -> CtorInfo -> CT -> CT -> [(Int, CT)]
fieldMemberships known d c k h = catMaybes (zipWith one [0 ..] (ctorFields c))
  where
    self = renderQualName (dataQual d)
    one j = \case
      TData n _
        | n == self -> Just (j, CSym "at" [h, k, fieldT j k])
        | Just isCore <- known n -> Just (j, CSym isCore [fieldT j k])
      _ -> Nothing

-- | The step function of the membership predicate, as a schema parameter.
membershipLambda :: (Text -> Maybe Text) -> DataInfo -> Text
membershipLambda known d = "{λ k h. " <> render (membershipBody known d (CVar "k") (CVar "h")) <> "}"

{- |
The definitions and lemmas of a data type, given the membership predicates
of the data types encoded before it.
-}
encodeData :: (Text -> Maybe Text) -> DataInfo -> Encoded
encodeData known d = Encoded equations lemmas members
  where
    ctors = dataCtors d
    isCore = dataIs d
    lam = membershipLambda known d
    equations =
      [ render (CSym (ctorCore c) [CVar ("a" <> T.pack (show j)) | j <- [0 .. length (ctorFields c) - 1]]) `withoutParens` c
          <> " = "
          <> render (consSeq (toInteger (ctorIndex c)) [CVar ("a" <> T.pack (show j)) | j <- [0 .. length (ctorFields c) - 1]])
      | c <- ctors
      ]
        <> [isCore <> " n = " <> if null ctors then "0" else "cvrec " <> lam <> " n"]
    -- An equation's left side is the name and its arguments, unparenthesised.
    withoutParens t c = if null (ctorFields c) then t else T.drop 1 (T.dropEnd 1 t)

    lemmas = concatMap ctorLemmas ctors <> collapses <> membership <> [inversion]
    members = [(ctorCore c, [(j, memberOf code) | (j, code) <- fieldMemberships known d c (CVar "k") (CVar "h")]) | c <- ctors]

    ctorLemmas c =
      let k = length (ctorFields c)
          vs = map var [0 .. k - 1]
          applied = CSym (ctorCore c) vs
          seqs = [consSeq' m | m <- [0 .. k + 1]]
          -- the sequence with its first m elements dropped
          consSeq' m = foldr (\x acc -> CSym "cons" [x, acc]) (CNum 0) (drop m (CNum (fromIntegral (ctorIndex c)) : vs))
          defName = ctorLemma c "def"
          haveE = "have E: (" <> render applied <> " = " <> render (seqs !! 0) <> ") { exact " <> defName <> " }; "
          fieldLemma j =
            ( ctorLemma c ("field-" <> T.pack (show j))
            , theorem (ctorLemma c ("field-" <> T.pack (show j))) [] (eqn (fieldT j applied) (vs !! j)) $
                haveE
                  <> "calc "
                  <> render (fieldT j applied)
                  <> " = "
                  <> render (fieldT j (seqs !! 0))
                  <> " by cong E"
                  <> T.concat [" = " <> render (hdT (iterate tlT (seqs !! (m + 1)) !! (j - m))) <> " by cong tlCons" | m <- [0 .. j]]
                  <> " = "
                  <> render (vs !! j)
                  <> " by exact hdCons"
            )
          ltLemma j =
            ( ctorLemma c ("lt-" <> T.pack (show j))
            , theorem (ctorLemma c ("lt-" <> T.pack (show j))) [] (ltT (vs !! j) applied) $
                haveE
                  <> "have L"
                  <> T.pack (show (j + 1))
                  <> ": "
                  <> ltT (vs !! j) (seqs !! (j + 1))
                  <> " { exact ltConsL }; "
                  <> T.concat
                    [ "have R"
                        <> T.pack (show m)
                        <> ": "
                        <> ltT (seqs !! (m + 1)) (seqs !! m)
                        <> " { exact ltConsR }; "
                        <> "have L"
                        <> T.pack (show m)
                        <> ": "
                        <> ltT (vs !! j) (seqs !! m)
                        <> " { exact ltTrans on L"
                        <> T.pack (show (m + 1))
                        <> " R"
                        <> T.pack (show m)
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
    cvrecAt x = CRaw ("cvrec " <> lam <> " " <> render x)
    histAt' x = CRaw ("hist " <> lam <> " " <> render x)
    membership
      | null ctors = []
      | otherwise =
          [ (dataLemma d "is-def", theorem (dataLemma d "is-def") [] (eqn (CSym isCore [n]) (cvrecAt n)) "refl")
          , (dataLemma d "is-beta", theorem (dataLemma d "is-beta") [] (eqn (cvrecAt n) (membershipBody known d n (histAt' n))) "refl")
          ]

    -- 0 < T.is t |- the disjunction of the shapes t may have, with the memberships of their fields.
    inversion = (dataLemma d "inversion", theorem (dataLemma d "inversion") [membershipText isCore t] (disjunction (map disjunct ctors)) script)
    disjunct c =
      let fs = [fieldT j t | j <- [0 .. length (ctorFields c) - 1]]
          eqT = "(" <> render t <> " = " <> render (CSym (ctorCore c) fs) <> ")"
          mems = [membershipText (memberOf m) (fieldT j t) | (j, m) <- fieldMemberships known d c t (histAt' t)]
       in conjunction (eqT : mems)
    memberOf = \case
      CSym "at" _ -> isCore
      CSym other _ -> other
      _ -> isCore
    disjunction = \case
      [] -> "_|_"
      [x] -> x
      x : xs -> "(" <> x <> " \\/ " <> disjunction xs <> ")"
    conjunction = \case
      [x] -> x
      x : xs -> "(" <> x <> " /\\ " <> conjunction xs <> ")"
      [] -> "(0 = 0)"

    body = membershipBody known d t (histAt' t)
    rest i = foldr (\(j, b) acc -> CSym "ifte" [CSym "eq" [hdT t, CNum j], b, acc]) (CNum 0) (drop i (zip [0 ..] (branches t)))
    branches x = [branchOf c x | c <- ctors]
    branchOf c x = case membershipBody known d x (histAt' x) of
      b -> nth (ctorIndex c) b
    -- The branch of a dispatch at an index.
    nth i = \case
      CSym "ifte" [_, b, more] -> if i == 0 then b else nth (i - 1) more
      other -> other

    script
      | null ctors = "have V: (" <> render (CSym isCore [t]) <> " = 0) { refl }; have W: ((lt 0 0) = 1) { calc (lt 0 0) = (lt 0 " <> render (CSym isCore [t]) <> ") by cong V = 1 by exact H1 }; exact zeroPosAbsurd"
      | otherwise =
          "have V0: ("
            <> render (CSym isCore [t])
            <> " = "
            <> render body
            <> ") { calc "
            <> render (CSym isCore [t])
            <> " = "
            <> render (cvrecAt t)
            <> " by exact "
            <> dataLemma d "is-def"
            <> " = "
            <> render body
            <> " by exact "
            <> dataLemma d "is-beta"
            <> " }; "
            <> caseAt 0
    isT = render (CSym isCore [t])
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
    -- From 0 < the branch of c: the equation and the memberships, then the disjunct of c.
    extract c br =
      let mems = fieldMemberships known d c t (histAt' t)
          ctorApplied = CSym (ctorCore c) [fieldT j t | j <- [0 .. length (ctorFields c) - 1]]
          eqCode = CSym "eq" [t, ctorApplied]
          start = "have P: ((lt 0 " <> render br <> ") = 1) { calc (lt 0 " <> render br <> ") = (lt 0 " <> isT <> ") by cong W = 1 by exact H1 }; "
          splitEq = case mems of
            [] -> "have E: (" <> render t <> " = " <> render ctorApplied <> ") { exact eqElim }; "
            _ ->
              "have Pe: ((lt 0 "
                <> render eqCode
                <> ") = 1) { exact conjElim1 on P }; have Pm: ((lt 0 "
                <> render (conjsOf (map snd mems))
                <> ") = 1) { exact conjElim2 on P }; have E: ("
                <> render t
                <> " = "
                <> render ctorApplied
                <> ") { exact eqElim on Pe }; "
          conjsOf = \case
            [m] -> m
            m : ms -> CSym "conj" [m, conjsOf ms]
            [] -> CNum 1
          -- K1 … the memberships' codes, from Pm by conjElim.
          memCodes = splitConj "Pm" (map snd mems) (1 :: Int)
          splitConj h ms idx = case ms of
            [] -> ""
            [_] -> "have K" <> show' idx <> ": ((lt 0 " <> render (head ms) <> ") = 1) { exact " <> h <> " }; "
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
          memProofs = T.concat (zipWith memProof [1 :: Int ..] mems)
          memProof idx (j, code) = case code of
            CSym "at" [hh, _, f] ->
              "have Lf"
                <> show' idx
                <> ": "
                <> ltT f ctorApplied
                <> " { exact "
                <> ctorLemma c ("lt-" <> T.pack (show j))
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
                <> membershipText isCore f
                <> " { calc (lt 0 "
                <> render (CSym isCore [f])
                <> ") = (lt 0 "
                <> render (cvrecAt f)
                <> ") by cong "
                <> dataLemma d "is-def"
                <> " = (lt 0 "
                <> render (CSym "at" [hh, t, f])
                <> ") by cong Ha"
                <> show' idx
                <> " = 1 by exact K"
                <> show' idx
                <> " }; "
            _ -> "have M" <> show' idx <> ": " <> membershipText (memberOf code) (fieldT j t) <> " { exact K" <> show' idx <> " }; "
          conclude = case mems of
            [] -> "exact E"
            _ -> conjR ("E" : ["M" <> show' idx | idx <- [1 .. length mems]])
          conjR = \case
            [x] -> "exact " <> x
            x : xs -> "ConjR { exact " <> x <> " } { " <> conjR xs <> " }"
            [] -> "skip"
          select = T.concat (replicate (ctorIndex c) "DisjR1; ") <> (if ctorIndex c < length ctors - 1 then "DisjR2; " else "")
       in start <> splitEq <> memCodes <> memProofs <> select <> conclude

    theorem name hyps statement proof = "theorem " <> name <> " : " <> T.intercalate ", " hyps <> " |- " <> statement <> "\nby " <> proof
    eqn a b = "(" <> render a <> " = " <> render b <> ")"
    ltT a b = "((lt " <> render a <> " " <> render b <> ") = 1)"
    show' :: (Show s) => s -> Text
    show' = T.pack . show
