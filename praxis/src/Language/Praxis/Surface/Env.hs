{-# LANGUAGE OverloadedStrings #-}

{- |
The global environment of a module: its data types, constructors, functions
and theorems, the namespaces they open, and the resolution of names.

Namespaces follow Rust: a data type @T@ opens the namespace @T@ holding its
constructors, @T.C@; a function @f@ opens the namespace @f@ holding the
lemmas generated for it, @f.unfold-Nil@; @open T@, as in Agda, brings the
members of @T@ into unqualified scope.  An unqualified name is resolved, in
order, as a variable of the local context (by the caller), a top-level name
of the module, a member of an opened namespace, and then a constructor: of
the expected type when one is known, or the only constructor of that name.
Every global has a core name, "Language.Praxis.Surface.Mangle".
-}
module Language.Praxis.Surface.Env (
  -- * Globals
  QualName,
  DataInfo (..),
  CtorInfo (..),
  FunInfo (..),
  TheoremInfo (..),
  ClassInfo (..),
  MethodInfo (..),
  LawInfo (..),
  InstanceInfo (..),
  Slot (..),
  staticSlots,
  valueSlots,
  staticName,
  membershipSlot,
  isMembershipSlot,
  Premise (..),
  Global (..),
  globalQualName,
  globalCore,
  renderQualName,

  -- * Environments
  Env (..),
  emptyEnv,
  qualify,
  addData,
  addFunction,
  addTheorem,
  addClass,
  addLaws,
  addInstanceFunction,
  addInstance,
  addNamespaceMember,
  openNamespace,

  -- * Resolution
  resolve,
  constructorsNamed,
  dataOfCtor,
  displayName,
) where

import Bound (Scope)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.Surface.Mangle (mangleGlobal)
import Language.Praxis.Surface.Syntax (Expr)
import Language.Praxis.Surface.Syntax.Raw (Located, QName (..), Segment (..), segmentText)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Kind, Scheme, Ty)

-- * Globals

-- | A qualified name as its segments: the module's, the namespaces', then the name itself.
type QualName = [Segment]

renderQualName :: QualName -> Text
renderQualName = T.intercalate "." . map segmentText

data DataInfo = DataInfo
  { dataQual :: !QualName
  , dataParams :: ![(Text, Kind)]
  , dataCtors :: ![CtorInfo]
  , dataIs :: !Text
  -- ^ the core name of the membership predicate
  }
  deriving stock (Show)

data CtorInfo = CtorInfo
  { ctorQual :: !QualName
  , ctorData :: !QualName
  , ctorIndex :: !Int
  , ctorFields :: ![Ty]
  -- ^ over the parameters of the data type
  , ctorCore :: !Text
  }
  deriving stock (Show)

data FunInfo = FunInfo
  { funQual :: !QualName
  , funScheme :: !Scheme
  , funArity :: !Int
  , funCore :: !Text
  , funSlots :: ![Slot]
  -- ^ its dictionary, in order: the methods its constraints give it which it uses
  }
  deriving stock (Show)

{- |
A place of a function's dictionary: a method of a class at one of the
function's type parameters, and the method's arity.  A method taking
arguments is a parameter of the function's schema, 'staticName'; one taking
none, a value, is an argument after the function's own.
-}
data Slot = Slot
  { slotMethod :: !QualName
  , slotParam :: !Int
  , slotArity :: !Int
  }
  deriving stock (Show, Eq)

-- | The places of a dictionary which are the parameters of a schema: the methods taking arguments.
staticSlots :: [Slot] -> [Slot]
staticSlots = filter ((> 0) . slotArity)

-- | The places of a dictionary which are values: the methods taking no argument.
valueSlots :: [Slot] -> [Slot]
valueSlots = filter ((== 0) . slotArity)

-- | The name of the schema parameter of a function at its place among the parameters, from 1.
staticName :: Int -> Text
staticName j = "w_" <> T.pack (show j)

{- |
The place of a dictionary for the membership predicate of a type parameter
which a class with laws constrains: a parameter of the schema, of one
argument, which the values of that type are members by.
-}
membershipSlot :: Int -> Slot
membershipSlot i = Slot [Ident "#is"] i 1

isMembershipSlot :: Slot -> Bool
isMembershipSlot s = slotMethod s == [Ident "#is"]

{- |
A premise of a theorem under constraints: a law of a class at one of the
theorem's type parameters, or the closure of a method there, that its
results are members of the parameter's type.
-}
data Premise
  = PLaw !QualName !Int
  | PClosure !QualName !Int
  deriving stock (Show, Eq)

{- |
A theorem, or a lemma the elaborator generated: its core name, and the
number of values its statement quantifies over, which an application of it
in a proof may give as arguments, in order.
-}
data TheoremInfo = TheoremInfo
  { thmQual :: !QualName
  , thmCore :: !Text
  , thmBinders :: ![Text]
  -- ^ the core variables of its statement, in the order of its binders
  , thmMembered :: ![Ty]
  {- ^ the types of its binders, in order, when its statement gives each
  value of a data type the hypothesis of its membership; none for a lemma
  which holds for all codes
  -}
  , thmSlots :: ![Slot]
  -- ^ the dictionary of its constraints, the places its statement uses
  , thmPremises :: ![Premise]
  -- ^ the premises of the rule it is, in order: laws and closures at its type parameters
  , thmStatement :: !(Maybe (Scope Int Expr Void))
  -- ^ its proposition, over its binders, its methods the places of 'thmSlots'; none for a generated lemma
  }
  deriving stock (Show)

-- | A class: its superclasses, by their qualified names, its methods, in order, and its laws.
data ClassInfo = ClassInfo
  { classQual :: !QualName
  , classSuperclasses :: ![QualName]
  , classMethods :: ![MethodInfo]
  , classLaws :: ![LawInfo]
  }
  deriving stock (Show)

{- |
A law of a class: a statement each instance proves, over values of the
class's parameter and of types over it, whose methods are the places of the
class's dictionary at its parameter.
-}
data LawInfo = LawInfo
  { lawQual :: !QualName
  , lawClass :: !QualName
  , lawBinders :: ![(Text, Ty)]
  -- ^ the values it quantifies over, their types over the class's parameter alone
  , lawProp :: !(Scope Int Expr Void)
  -- ^ its proposition, over the binders, its methods the places of 'lawSlots'
  , lawSlots :: ![Slot]
  -- ^ the dictionary of the class at its parameter: each method of it and of its superclasses
  , lawBody :: !(Located R.Expr)
  -- ^ its proposition as written, which an instance elaborates at its type
  }
  deriving stock (Show)

{- |
A method of a class: its class, its scheme — the class's parameter its first
type parameter — and the number of arguments it is applied to.
-}
data MethodInfo = MethodInfo
  { methodQual :: !QualName
  , methodClass :: !QualName
  , methodScheme :: !Scheme
  , methodArity :: !Int
  }
  deriving stock (Show)

{- |
An instance: its class, the head of the type it is for — the qualified name
of a data type, or @Nat@ — and the function defining each method, by the
method's qualified name.
-}
data InstanceInfo = InstanceInfo
  { instQual :: !QualName
  , instClass :: !QualName
  , instHead :: !Text
  , instFunctions :: !(Map QualName FunInfo)
  , instLaws :: !(Map QualName TheoremInfo)
  -- ^ the theorem proving each law of the class at the instance's type, by the law's qualified name
  }
  deriving stock (Show)

data Global
  = GData !DataInfo
  | GCtor !CtorInfo
  | GFun !FunInfo
  | GTheorem !TheoremInfo
  | GClass !ClassInfo
  | GMethod !MethodInfo
  | GLaw !LawInfo
  | GInstance !InstanceInfo
  deriving stock (Show)

globalQualName :: Global -> QualName
globalQualName = \case
  GData d -> dataQual d
  GCtor c -> ctorQual c
  GFun f -> funQual f
  GTheorem t -> thmQual t
  GClass c -> classQual c
  GMethod m -> methodQual m
  GLaw l -> lawQual l
  GInstance i -> instQual i

-- | The core name of a global: its symbol, or its lemma; a class, a method and an instance have none of their own.
globalCore :: Global -> Text
globalCore = \case
  GData d -> dataIs d
  GCtor c -> ctorCore c
  GFun f -> funCore f
  GTheorem t -> thmCore t
  g -> coreOf (globalQualName g)

-- * Environments

data Env = Env
  { envModule :: !QualName
  , envGlobals :: !(Map QualName Global)
  , envTop :: !(Map Segment QualName)
  -- ^ the top-level names of the module, unqualified
  , envNamespaces :: !(Map QualName (Map Segment QualName))
  -- ^ each namespace by its owner, with its members
  , envOpened :: ![QualName]
  , envDisplay :: !(Map Text Text)
  -- ^ every core name, with the surface name it stands for
  , envInstances :: !(Map (QualName, Text) InstanceInfo)
  -- ^ each instance, by its class and the head of its type: one for each
  }

emptyEnv :: QualName -> Env
emptyEnv m = Env m Map.empty Map.empty Map.empty [] Map.empty Map.empty

-- | A name of the module, qualified.
qualify :: Env -> [Segment] -> QualName
qualify env segs = envModule env <> segs

-- | The core name of a qualified name.
coreOf :: QualName -> Text
coreOf = mangleGlobal . map segmentText'
  where
    segmentText' = \case
      Ident t -> t
      Op t -> t

-- | Add a data type and its constructors; the type opens a namespace holding them.
addData :: Env -> Segment -> [(Text, Kind)] -> [(Segment, [Ty])] -> (Env, DataInfo)
addData env name params ctors = (env', info)
  where
    q = qualify env [name]
    info = DataInfo q params [CtorInfo (q <> [c]) q i fs (coreOf (q <> [c])) | (i, (c, fs)) <- zip [0 ..] ctors] (coreOf (q <> [Ident "is"]))
    members = Map.fromList [(c, q <> [c]) | (c, _) <- ctors]
    env' =
      env
        { envGlobals = Map.insert q (GData info) (foldr (\c -> Map.insert (ctorQual c) (GCtor c)) (envGlobals env) (dataCtors info))
        , envTop = Map.insert name q (envTop env)
        , envNamespaces = Map.insertWith Map.union q members (envNamespaces env)
        , envDisplay = Map.union (Map.fromList ((dataIs info, renderQualName (q <> [Ident "is"])) : [(ctorCore c, segmentText (last (ctorQual c))) | c <- dataCtors info])) (envDisplay env)
        }

-- | Add a function, with its dictionary; it opens a namespace for its lemmas.
addFunction :: Env -> Segment -> Scheme -> Int -> [Slot] -> (Env, FunInfo)
addFunction env name sch arity slots = (env', info)
  where
    q = qualify env [name]
    info = FunInfo q sch arity (coreOf q) slots
    env' =
      env
        { envGlobals = Map.insert q (GFun info) (envGlobals env)
        , envTop = Map.insert name q (envTop env)
        , envNamespaces = Map.insertWith Map.union q Map.empty (envNamespaces env)
        , envDisplay = Map.insert (funCore info) (segmentText name) (envDisplay env)
        }

{- |
Add a theorem, at the qualified name given, whose core name is derived from
it, with the types of its values when its statement gives them memberships;
a top-level one is also a top-level name.
-}
addTheorem :: Env -> QualName -> [Text] -> [Ty] -> [Slot] -> [Premise] -> Maybe (Scope Int Expr Void) -> (Env, TheoremInfo)
addTheorem env q binders membered slots premises statement = (env', info)
  where
    info = TheoremInfo q (coreOf q) binders membered slots premises statement
    top = case drop (length (envModule env)) q of
      [n] | take (length (envModule env)) q == envModule env -> Map.insert n q
      _ -> id
    env' =
      env
        { envGlobals = Map.insert q (GTheorem info) (envGlobals env)
        , envTop = top (envTop env)
        , envDisplay = Map.insert (thmCore info) (renderQualName (drop (length (envModule env)) q)) (envDisplay env)
        }

{- |
Add a class and its methods.  The class opens a namespace holding its
methods, and each method, as in Haskell, is also a top-level name.
-}
addClass :: Env -> Segment -> [QualName] -> [(Segment, Scheme, Int)] -> (Env, ClassInfo)
addClass env name supers methods = (env', info)
  where
    q = qualify env [name]
    info = ClassInfo q supers [MethodInfo (q <> [m]) q sch arity | (m, sch, arity) <- methods] []
    env' =
      env
        { envGlobals = foldr (\m -> Map.insert (methodQual m) (GMethod m)) (Map.insert q (GClass info) (envGlobals env)) (classMethods info)
        , envTop = foldr (\(m, _, _) -> Map.insert m (q <> [m])) (Map.insert name q (envTop env)) methods
        , envNamespaces = Map.insertWith Map.union q (Map.fromList [(m, q <> [m]) | (m, _, _) <- methods]) (envNamespaces env)
        }

-- | Add the laws of a class: each, as a method is, a top-level name and a member of the class's namespace.
addLaws :: QualName -> [LawInfo] -> Env -> Env
addLaws cq laws env =
  env
    { envGlobals = foldr (\l -> Map.insert (lawQual l) (GLaw l)) (Map.adjust withLaws cq (envGlobals env)) laws
    , envTop = foldr (\l -> Map.insert (last (lawQual l)) (lawQual l)) (envTop env) laws
    , envNamespaces = Map.insertWith Map.union cq (Map.fromList [(last (lawQual l), lawQual l) | l <- laws]) (envNamespaces env)
    }
  where
    withLaws = \case
      GClass c -> GClass c {classLaws = classLaws c <> laws}
      g -> g

{- |
The function defining a method in an instance: a member of the instance's
namespace by the method's name, which opens a namespace of its own for its
lemmas, as a function does.
-}
addInstanceFunction :: Env -> QualName -> Segment -> Scheme -> Int -> [Slot] -> (Env, FunInfo)
addInstanceFunction env instance' method sch arity slots = (env', info)
  where
    q = instance' <> [method]
    info = FunInfo q sch arity (coreOf q) slots
    env' =
      env
        { envGlobals = Map.insert q (GFun info) (envGlobals env)
        , envNamespaces = Map.insertWith Map.union instance' (Map.singleton method q) (Map.insertWith Map.union q Map.empty (envNamespaces env))
        , envDisplay = Map.insert (funCore info) (renderQualName (drop (length (envModule env)) q)) (envDisplay env)
        }

-- | Add an instance: a top-level name, whose namespace holds the functions of its methods.
addInstance :: Env -> InstanceInfo -> Env
addInstance env inst =
  env
    { envGlobals = Map.insert (instQual inst) (GInstance inst) (envGlobals env)
    , envTop = Map.insert (last (instQual inst)) (instQual inst) (envTop env)
    , envInstances = Map.insert (instClass inst, instHead inst) inst (envInstances env)
    }

-- | Make a global a member of a namespace, by the name given.
addNamespaceMember :: QualName -> Segment -> QualName -> Env -> Env
addNamespaceMember owner member q env =
  env {envNamespaces = Map.insertWith Map.union owner (Map.singleton member q) (envNamespaces env)}

-- | Open a namespace, as @open T@ does.
openNamespace :: QualName -> Env -> Env
openNamespace q env = env {envOpened = envOpened env <> [q]}

-- * Resolution

{- |
The globals a name may refer to, in the order of preference: a qualified
name through its namespaces (or from the module's own name); an unqualified
one as a top-level name, then as a member of an opened namespace.
Constructors by expected type are the caller's to try, 'constructorsNamed'.
-}
resolve :: Env -> QName -> [Global]
resolve env (QName quals base) = case quals of
  [] ->
    firstNonEmpty
      [ maybe [] (lookupQ . pure) (Map.lookup base (envTop env))
      , concat [lookupQ (Map.lookup base =<< Map.lookup o (envNamespaces env)) | o <- envOpened env]
      ]
  q : qs ->
    firstNonEmpty
      [ viaNamespace (Map.lookup q (envTop env)) qs
      , lookupQ (Just (quals <> [base]))
      , lookupQ (Just (envModule env <> quals <> [base]))
      ]
  where
    lookupQ = \case
      Just q -> maybe [] pure (Map.lookup q (envGlobals env))
      Nothing -> []
    viaNamespace owner rest = case owner of
      Nothing -> []
      Just o -> case rest of
        [] -> lookupQ (Map.lookup base =<< Map.lookup o (envNamespaces env))
        r : rs -> viaNamespace (Map.lookup r =<< Map.lookup o (envNamespaces env)) rs
    firstNonEmpty = \case
      [] -> []
      xs : rest -> if null xs then firstNonEmpty rest else xs

-- | Every constructor of that unqualified name, of whichever type.
constructorsNamed :: Env -> Segment -> [CtorInfo]
constructorsNamed env s = mapMaybe ctor (Map.elems (envGlobals env))
  where
    ctor = \case
      GCtor c | last (ctorQual c) == s -> Just c
      _ -> Nothing

-- | The data type of a constructor.
dataOfCtor :: Env -> CtorInfo -> Maybe DataInfo
dataOfCtor env c = case Map.lookup (ctorData c) (envGlobals env) of
  Just (GData d) -> Just d
  _ -> Nothing

-- | The surface name a core name stands for, when it stands for one.
displayName :: Env -> Text -> Maybe Text
displayName env n = Map.lookup n (envDisplay env)
