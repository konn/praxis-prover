{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Praxis.PRA.Syntax (
  Term (Var, Lit, App, (:$)),
  Atomic (..),
  (===),
  Formula (..),
  (/\),
  (\/),
  (==>),
  Sequent (..),
  (|-),
  Substitutable (..),
  canonicalise,
  suc,
  var,
  lit,

  -- * Abstract functions
  abstractFunction,
  abstractName,
  functionMetas,
  Abstraction (..),
  abstraction,
  applyAbstraction,
  abstractionAt,
  compileTerm,
) where

import Control.Lens (prism', review)
import Data.Foldable qualified as Foldable
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.List qualified as L
import Data.Multiset (Multiset)
import Data.Proxy (Proxy (..))
import Data.Sized
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality
import Data.Type.Natural hiding (Succ, Zero)
import Data.Type.Ordinal
import Data.Vector qualified as V
import GHC.Generics
import GHC.TypeNats (KnownNat, SomeNat (..), someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion.Code hiding (suc)
import Language.Praxis.PRA.PrimitiveRecursion.Function (Function (..))
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Numeric.Natural

data Term a where
  Var :: !a -> Term a
  Lit :: !Natural -> Term a
  App :: (KnownNat n) => !(Function n) -> !(V n (Term a)) -> Term a

-- | Compatibility constructor for applications of bare PRA code.
pattern (:$) :: () => (KnownNat n) => PRFCode n -> V n (Term a) -> Term a
pattern code :$ args = App (Primitive code) args

{- | The successor, canonicalised: a numeral steps to the next numeral, so a
syntactic @Succ@ survives only in front of a term which is not itself a
numeral.  This is the invariant the 'Evalable' instance below documents, and
which "Language.Praxis.PRA.Equality" decides against.
-}
suc :: Term a -> Term a
{-# INLINE suc #-}
suc = review _Succ

lit :: Natural -> Term a
{-# INLINE lit #-}
lit = Lit

var :: a -> Term a
{-# INLINE var #-}
var = Var

instance (Show a) => Show (Term a) where
  showsPrec d (Var x) = showParen (d > 10) (showString "Var " . showsPrec 11 x)
  showsPrec d (Lit n) = showParen (d > 10) (showString "Lit " . showsPrec 11 n)
  showsPrec d (App (Primitive f) xs) = showParen (d > 6) (showsPrec 7 f . showString " :$ " . showsPrec 7 xs)
  showsPrec d (App f xs) = showParen (d > 10) (showString "App " . showsPrec 11 f . showString " " . showsPrec 11 xs)

deriving instance Functor Term

deriving instance Foldable Term

deriving instance Traversable Term

{- |
Quotient out the redundancy in 'Term''s representation: a successor of a
numeral is the next numeral, and an application of 'Zero' is @'Lit' 0@ at every
arity.  These are the two ways the same numeral can be spelled, and this is
the invariant the 'Evalable' instance below describes.

This is deliberately /not/ evaluation.  @plus ':$' ['Lit' 2, 'Lit' 3]@ is left
alone; deciding that it denotes @'Lit' 5@ is the job of
'Language.Praxis.PRA.Equality.defEq', and of the @Defeq@ rule which appeals to
it.  Were canonicalisation to reduce, a proof could discharge an equation the
calculus requires @Defeq@ to justify.
-}
canonicalise :: Term a -> Term a
canonicalise t@Var {} = t
canonicalise t@Lit {} = t
canonicalise (Zero :$ _) = Lit 0
canonicalise (Succ :$ xs) = suc (canonicalise (sIndex [od|0|] xs))
canonicalise (App f xs) = App f (fmap canonicalise xs)

{- |
Equality identifies the spellings 'canonicalise' conflates, so a rule which
builds @'Lit' 4@ meets a context which spells it @'Succ' ':$' ['Lit' 3]@.  It
does not reduce: see 'canonicalise'.
-}
instance (Eq a) => Eq (Term a) where
  t1 == t2 = eqCanonical (canonicalise t1) (canonicalise t2)

-- | Structural equality, on terms already in canonical form.
eqCanonical :: (Eq a) => Term a -> Term a -> Bool
eqCanonical (Var x1) (Var x2) = x1 == x2
eqCanonical Var {} _ = False
eqCanonical (Lit n1) (Lit n2) = n1 == n2
eqCanonical Lit {} _ = False
eqCanonical (App (f1 :: Function m) xs1) (App (f2 :: Function m') xs2) =
  case testEquality (sNat @m) (sNat @m') of
    Nothing -> False
    Just Refl -> f1 == f2 && V.and (V.zipWith eqCanonical (unsized xs1) (unsized xs2))
eqCanonical App {} _ = False

infix 6 :$

-- | Agrees with '(==)': both work on the canonical form.
instance (Hashable a) => Hashable (Term a) where
  hashWithSalt salt = hashCanonical salt . canonicalise

hashCanonical :: (Hashable a) => Int -> Term a -> Int
hashCanonical salt (Var x) = hashWithSalt salt (0 :: Int, x)
hashCanonical salt (Lit n) = hashWithSalt salt (1 :: Int, n)
hashCanonical salt (App f xs) =
  V.foldl' hashCanonical (hashWithSalt salt (2 :: Int, f)) (unsized xs)

{- | Terms are the syntactic model of the primitive-recursive numerals: an
application which cannot be reduced is kept as a
'Language.Praxis.PRA.PrimitiveRecursion.residual', which is what turns
'Language.Praxis.PRA.PrimitiveRecursion.evalPRFCodeM' into a partial evaluator
on open terms.

Numerals are canonicalised to 'Lit', so 'Succ' only survives in front of a term
which is not itself a numeral.  Consequently the prisms are lawful only up to
definitional equality — rebuilding a matched @'Succ' ':$' ['Lit' n]@ yields
@'Lit' (n + 1)@ — which is precisely the equivalence
"Language.Praxis.PRA.Equality" decides.
-}
instance Evalable (Term a) where
  _Zero = prism' (const $ Lit 0) \case
    Lit 0 -> Just ()
    -- 'Zero' denotes the constant @0@ at every arity, so it is a numeral
    -- whatever it is applied to — including @'Zero' ':$' 'SV.Nil'@.
    Zero :$ _ -> Just ()
    _ -> Nothing
  _Succ =
    prism'
      \case
        Lit n -> Lit (n + 1)
        t -> Succ :$ SV.singleton t
      \case
        Lit n | n > 0 -> Just $ Lit (n - 1)
        Succ :$ args -> Just $ sIndex [od|0|] args
        _ -> Nothing
  fromNatural = Lit
  residual = (:$)

data Atomic a = !(Term a) :=== !(Term a)
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

class (Functor t) => Substitutable t where
  subst :: (Eq a) => a -> Term a -> t a -> t a

instance Substitutable Term where
  subst x t (Var y)
    | x == y = t
    | otherwise = Var y
  subst _ _ (Lit n) = Lit n
  subst x t (App f xs) = App f (fmap (subst x t) xs)

instance Substitutable Atomic where
  subst x t (t1 :=== t2) = subst x t t1 :=== subst x t t2

instance Substitutable Formula where
  subst x t (Atm p) = Atm $ subst x t p
  subst x t (f1 :/\ f2) = subst x t f1 :/\ subst x t f2
  subst x t (f1 :\/ f2) = subst x t f1 :\/ subst x t f2
  subst x t (f1 :==> f2) = subst x t f1 :==> subst x t f2
  subst _ _ Bot = Bot

data Formula a
  = Atm !(Atomic a)
  | !(Formula a) :/\ !(Formula a)
  | !(Formula a) :\/ !(Formula a)
  | !(Formula a) :==> !(Formula a)
  | Bot
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

(===) :: Term a -> Term a -> Formula a
(===) = fmap Atm . (:===)

infix 5 :===, ===

(/\) :: Formula a -> Formula a -> Formula a
(/\) = (:/\)

infixr 4 :/\, /\

(\/) :: Formula a -> Formula a -> Formula a
(\/) = (:\/)

infixr 3 :\/, \/

(==>) :: Formula a -> Formula a -> Formula a
(==>) = (:==>)

infixr 2 :==>, ==>

data Sequent a = !(Multiset (Formula a)) :|- !(Formula a)
  deriving (Show, Eq, Generic)
  deriving anyclass (Hashable)

(|-) :: Multiset (Formula a) -> Formula a -> Sequent a
(|-) = (:|-)

infix 1 |-, :|-

-- * Abstract functions

{- |
A function known by name only: what a term metavariable with parameters
stands for in the statement of a derived rule, applied as @p(t)@ or standing
as the parameter of a schema, @mu {p} b@.  Its identity records its name
and the names of its parameters; its arity is their number.
-}
abstractFunction :: String -> [String] -> F.SomeFunction
abstractFunction n ps = case someNatVal (fromIntegral (L.length ps)) of
  SomeNat (_ :: Proxy k) -> F.SomeFunction (Abstract (F.DefId (T.pack (n <> "«" <> L.unwords ps <> "»"))) :: Function k)

-- | The name and the parameters of an abstract function, and 'Nothing' for any other function.
abstractName :: Function n -> Maybe (String, [String])
abstractName = \case
  Abstract (F.DefId txt) -> decodeAbstract txt
  _ -> Nothing

decodeAbstract :: T.Text -> Maybe (String, [String])
decodeAbstract txt = case L.break (== '«') (T.unpack txt) of
  (n, '«' : rest) | not (L.null n), not (L.null rest), L.last rest == '»' -> Just (n, L.words (L.init rest))
  _ -> Nothing

{- |
The abstract functions a term mentions, with their parameters: applied, or
as the parameter of a schema instantiated at them, inside the code of the
instance.
-}
functionMetas :: Term a -> [(String, [String])]
functionMetas = L.nub . go
  where
    go = \case
      Var _ -> []
      Lit _ -> []
      App f xs -> mapMaybe' decodeAbstract (F.opaqueCalls (F.functionProgram f)) <> concatMap go (Foldable.toList xs)
    mapMaybe' g = foldr (\x acc -> maybe acc (: acc) (g x)) []

{- |
What a term metavariable with parameters is instantiated by.  As a term, a
body over placeholder variables for the parameters, which an application
@p(t1, …, tk)@ substitutes for; as a function, the closed code of that body
over the parameters and then the variables it captures, with the terms to
pass for those, which an instance of a schema at the function takes as
further arguments.  The two agree: the body is the code applied to the
parameters and the captured terms.
-}
data Abstraction a = Abstraction
  { abstractionParameters :: ![a]
  , abstractionBody :: !(Term a)
  , abstractionFunction :: !F.SomeFunction
  , abstractionCaptured :: ![Term a]
  }
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

{- |
The abstraction of a term over parameters: the variables of the term which
are not parameters are captured, in the order they first occur.
-}
abstraction :: (Eq a) => [a] -> Term a -> Abstraction a
abstraction params body = Abstraction params body (compileTerm (params <> captured) body) (L.map Var captured)
  where
    captured = L.filter (`L.notElem` params) (L.nub (Foldable.toList body))

-- | The abstraction applied: its body with the arguments substituted for the parameters, at once; 'Nothing' for the wrong number of them.
applyAbstraction :: (Eq a) => Abstraction a -> [Term a] -> Maybe (Term a)
applyAbstraction a args
  | L.length args /= L.length (abstractionParameters a) = Nothing
  | otherwise = Just (go (abstractionBody a))
  where
    pairs = L.zip (abstractionParameters a) args
    go = \case
      Var y -> maybe (Var y) id (L.lookup y pairs)
      Lit n -> Lit n
      App f xs -> App f (fmap go xs)

-- | 'applyAbstraction', for arguments which are known to be as many as the parameters.
abstractionAt :: (Eq a) => Abstraction a -> [Term a] -> Term a
abstractionAt a args = case applyAbstraction a args of
  Just t -> t
  Nothing -> error ("Language.Praxis.PRA.Syntax.abstractionAt: " <> show (L.length args) <> " arguments for " <> show (L.length (abstractionParameters a)) <> " parameters")

{- |
A term over variables as the closed code over those variables, in the order
given: a variable is the projection of its slot, and every other symbol
keeps its code.  A variable which is not a slot is read as zero.
-}
compileTerm :: forall a. (Eq a) => [a] -> Term a -> F.SomeFunction
compileTerm slots body = case someNatVal (fromIntegral (L.length slots)) of
  SomeNat (_ :: Proxy n) -> F.SomeFunction (F.programFunction (go @n (canonicalise body)))
  where
    go :: forall n. (KnownNat n) => Term a -> F.Program n
    go = \case
      Var v -> case L.lookup v (L.zip slots (Foldable.toList (SV.generate (sNat @n) id :: V n (Ordinal n)))) of
        Just i -> F.Base (Proj i)
        Nothing -> F.Base Zero
      Lit k -> numeral k
      App f xs -> F.Comp (F.functionProgram f) (fmap go xs)
    numeral :: forall n. (KnownNat n) => Natural -> F.Program n
    numeral 0 = F.Base Zero
    numeral k = F.Comp (F.Base Succ) (SV.singleton (numeral (k - 1)))
