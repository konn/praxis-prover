{-# LANGUAGE OverloadedStrings #-}

{- |
The renamer: the scope of a module, and every name it writes resolved to
what it means, before anything is typed.

A module's scope follows Agda.  What it declares, and what the modules
enclosing it declare, is in unqualified scope; a data type's constructors
are in the namespace of the type, a class's methods and laws in unqualified
scope too.  @import M@ brings the exports of @M@ into scope qualified,
@M.x@, by the name after @as@ when one is given; @open N@ brings the
members of a namespace — a module, a data type, a class, an instance — into
unqualified scope, and @open N public@ exports them as well; both take
@using@, @hiding@ and @renaming@.  A module nested in another is a
namespace of it holding what it exports: what it declares outside
@private@, and what it opened @public@.

An unqualified name is, in order: a variable bound around it; a name
declared by the module or by one enclosing it; a member of an opened
namespace, ambiguous when several give it distinct globals which are not
all constructors; and otherwise as written, which is then a constructor
found by the type expected of it, a builtin, a lemma of the library, a
hypothesis, a type variable, or nothing, once typed.  A qualified name is
resolved through its first segments: a namespace in unqualified scope, an
imported module by the longest name in scope which starts it, or the
module's own name or an enclosing one, written out; the rest of its
segments navigate namespaces, checked where the renamer knows the members,
appended as written where it does not, a function's generated lemmas.

The result is the module with every reference to a global written as its
canonical name — its library, its module, the namespaces, then the name —
which "Language.Praxis.Surface.Env" looks up without any scope; the
declarations of nested modules are flattened, each with the module it
belongs to; imports and openings are gone.  Scope errors are reported here,
each failing the declaration it is in.
-}
module Language.Praxis.Surface.Rename (
  -- * Modules
  ModuleExports (..),
  Imports,
  moduleImports,

  -- * Renaming
  Renamed (..),
  RDecl (..),
  ScopeError (..),
  renameModule,
  moduleExports,
) where

import Control.Monad (foldM, forM, forM_, unless)
import Data.Bifunctor (first)
import Data.List (isPrefixOf, nub, sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Env (CtorInfo (..), Env (..), Global (..), QualName, displayQualName, isComponent)
import Language.Praxis.Surface.Fixity (Fixities, exportedFixities, isConnective, isRelation, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Shape (lhsParts, rawSpine)
import Language.Praxis.Surface.Syntax.Raw

-- * Modules

-- | What a module exports, for the modules importing it: its name, its members, and the fixities of the operators among them.
data ModuleExports = ModuleExports
  { meName :: !QualName
  , meMembers :: !(Map Segment QualName)
  , meFixities :: !Fixities
  }
  deriving stock (Show)

{- |
The modules a file's imports may refer to, each by the library written
before it, if any, and its name: its exports, or why it cannot be imported.
A build resolves them before the file is renamed; a file checked on its own
has none.
-}
type Imports = Map (Maybe Text, QualName) (Either String ModuleExports)

-- | The imports of a file, at any depth, in order: where each is, the library written, and the module.
moduleImports :: Module -> [(Span, Maybe Text, QualName)]
moduleImports = concatMap decl . moduleDecls
  where
    decl (Located _ d) = case d of
      DImport imp -> [one imp]
      DOpenImport imp _ -> [one imp]
      DModule _ ds -> concatMap decl ds
      DPrivate ds -> concatMap decl ds
      _ -> []
    one (Import lib (Located sp mq) _ _) = (sp, unLocated <$> lib, qnameSegments mq)

qnameSegments :: QName -> QualName
qnameSegments (QName qs b) = qs <> [b]

toQName :: QualName -> QName
toQName q = QName (init q) (last q)

-- * The result

-- | A module renamed: its name, its declarations with the modules they belong to, its nested modules with their exports, its own exports, and the modules whose constructors an unqualified name may be found among.
data Renamed = Renamed
  { rnModule :: !QualName
  , rnDecls :: ![RDecl]
  , rnModules :: ![(QualName, Map Segment QualName)]
  , rnExports :: !(Map Segment QualName)
  , rnVisible :: ![QualName]
  }

-- | A declaration renamed, with the module it belongs to: the file's, or one nested in it.
data RDecl = RDecl
  { rdOwner :: !QualName
  , rdDecl :: !(Located Decl)
  }

-- | A name which does not resolve, where it is written, and why.
data ScopeError = ScopeError !Span !String
  deriving stock (Show, Eq)

-- | What a module exports, given the fixities in force in it.
moduleExports :: Fixities -> Renamed -> ModuleExports
moduleExports fx rn = ModuleExports (rnModule rn) (rnExports rn) (exportedFixities fx (map segmentRaw (Map.keys (rnExports rn))))

-- * The scope

-- | What the renaming of a file reads: the fixities, the tables of the modules before, the imports resolved, and the constructors' names of the imported modules.
data Ctx = Ctx
  { cxFx :: !Fixities
  , cxEnv :: !Env
  , cxImports :: !Imports
  , cxImportedCtors :: !(Set Segment)
  }

-- | The scope at a point of the file.
data Scope = Scope
  { scModule :: !QualName
  -- ^ the module the declarations belong to: the file's, and the nested ones entered
  , scTop :: !(Map Segment QualName)
  -- ^ the names declared by the module and the modules enclosing it
  , scExports :: !(Map Segment QualName)
  , scPrivate :: !Bool
  , scOpened :: ![(QualName, Map Segment QualName)]
  , scImports :: !(Map QualName (Map Segment QualName))
  , scNamespaces :: !(Map QualName (Map Segment QualName))
  -- ^ the namespaces the file declares whose members are known: data types, classes, instances, nested modules
  , scModules :: ![(QualName, Map Segment QualName)]
  -- ^ the nested modules finished, latest first
  , scCtors :: !(Set Segment)
  -- ^ the names of the constructors the file declares
  , scCtorQuals :: !(Set QualName)
  , scErrors :: ![ScopeError]
  -- ^ latest first
  }

type Locals = Set Text

type RM = Either ScopeError

{- |
Rename a module, of the name given, its library first: against the tables
of the modules before, and the imports resolved for it.  The scope errors
come in the order they were found.
-}
renameModule :: Fixities -> Env -> Imports -> QualName -> Module -> (Renamed, [ScopeError])
renameModule fx env imports modQ m =
  let imported = [meName e | Right e <- Map.elems imports]
      visible = modQ : imported
      cx = Ctx fx env imports (Set.fromList [last (ctorQual c) | GCtor c <- Map.elems (envGlobals env), any (`isPrefixOf` ctorData c) imported])
      sc0 = Scope modQ Map.empty Map.empty False [] Map.empty Map.empty [] Set.empty Set.empty []
      (sc, decls) = renameLevel cx sc0 (moduleDecls m)
   in (Renamed modQ decls (reverse (scModules sc)) (scExports sc) visible, reverse (scErrors sc))

failed :: ScopeError -> Scope -> Scope
failed err sc = sc {scErrors = err : scErrors sc}

-- | A name declared by the module: in unqualified scope, and exported unless under @private@.
declare :: Segment -> QualName -> Scope -> Scope
declare name q sc =
  sc
    { scTop = Map.insert name q (scTop sc)
    , scExports = if scPrivate sc then scExports sc else Map.insert name q (scExports sc)
    }

-- | A namespace the file declares, with its members.
namespace :: QualName -> Map Segment QualName -> Scope -> Scope
namespace q members sc = sc {scNamespaces = Map.insert q members (scNamespaces sc)}

-- | The members of a namespace, when the renamer knows them: declared by the file, or by a module before.
namespaceMembers :: Ctx -> Scope -> QualName -> Maybe (Map Segment QualName)
namespaceMembers cx sc q = case Map.lookup q (scNamespaces sc) of
  Just members -> Just members
  Nothing -> Map.lookup q (envNamespaces (cxEnv cx))

-- | Whether a global is a constructor: one the file declares, or one of a module before.
isCtorQual :: Ctx -> Scope -> QualName -> Bool
isCtorQual cx sc q =
  Set.member q (scCtorQuals sc) || case Map.lookup q (envGlobals (cxEnv cx)) of
    Just (GCtor _) -> True
    _ -> False

-- | Whether a bare name is a constructor's, of a data type of the file or of a module imported.
isCtorName :: Ctx -> Scope -> Segment -> Bool
isCtorName cx sc s = Set.member s (scCtors sc) || Set.member s (cxImportedCtors cx)

-- | The globals an unqualified name means in scope: the one declared, else those the opened namespaces give it.
lookupBare :: Scope -> Segment -> [QualName]
lookupBare sc s = case Map.lookup s (scTop sc) of
  Just q -> [q]
  Nothing -> nub [q | (_, view) <- scOpened sc, Just q <- [Map.lookup s view]]

{- |
The names never resolved to a global: the builtins of the language, the
words of proof terms, and the operators of arithmetic, the relations and
the connectives.
-}
builtin :: Segment -> Bool
builtin = \case
  Ident x -> x `elem` ["S", "suc", "absurd", "Nat", "nat", "rfl", "refl", "cong"]
  Op o -> isRelation o || isConnective o || o `elem` ["+", "-", "*", "^", "⊤", "⊥"]
  Component _ -> True

-- | A hypothesis the engine names itself: the induction hypotheses, @IH@, @IH1@, ….
implicitHypothesis :: Text -> Bool
implicitHypothesis x = x == "IH" || ("IH" `T.isPrefixOf` x && T.all (`elem` ['0' .. '9']) (T.drop 2 x) && T.length x > 2)

isLocal :: Locals -> Segment -> Bool
isLocal locals = \case
  Ident x -> Set.member x locals || implicitHypothesis x
  _ -> False

-- | What a written name resolves to: its canonical name, or nothing, when it is no global.
data Resolution = Canonical !QName | Unchanged

{- |
Resolve a name.  An unqualified one: a local, a builtin, a global declared
or opened, or as written.  A qualified one, through its head: a namespace
in unqualified scope, an imported module, or the module's own name or an
enclosing one; the rest navigates namespaces.
-}
resolveName :: Ctx -> Scope -> Locals -> Span -> QName -> RM Resolution
resolveName cx sc locals sp q@(QName quals base) = case quals of
  []
    | isLocal locals base || builtin base -> pure Unchanged
    | otherwise -> case lookupBare sc base of
        [] -> pure Unchanged
        [g] -> pure (Canonical (toQName g))
        gs
          | all (isCtorQual cx sc) gs -> pure Unchanged
          | otherwise -> Left (ScopeError sp ("ambiguous: " <> T.unpack (segmentText base) <> " is " <> T.unpack (T.intercalate " and " (map displayQualName gs)) <> "; qualify it, or hide one"))
  h : rest -> case lookupBare sc h of
    [owner] -> navigate owner (rest <> [base])
    (_ : _ : _) -> Left (ScopeError sp ("ambiguous: " <> T.unpack (segmentText h) <> " names several namespaces; qualify it, or hide one"))
    [] -> case sortOn (negate . length . fst) [(k, view) | (k, view) <- Map.toList (scImports sc), k `isPrefixOf` full] of
      (k, view) : _ -> case drop (length k) full of
        [] -> Left (ScopeError sp ("the module " <> T.unpack (qnameText q) <> " is no name"))
        r : rs -> case Map.lookup r view of
          Just g -> navigate g rs
          Nothing -> Left (ScopeError sp ("no " <> T.unpack (segmentText r) <> " in the module " <> T.unpack (T.intercalate "." (map segmentText k)) <> " as imported"))
      []
        | any (`isPrefixOf` quals) enclosing -> pure (Canonical (QName (component <> quals) base))
        | otherwise -> Left (ScopeError sp ("not in scope: " <> T.unpack (segmentText h) <> ", qualifying " <> T.unpack (qnameText q)))
  where
    full = quals <> [base]
    component = takeWhile isComponent (scModule sc)
    segs = dropWhile isComponent (scModule sc)
    enclosing = [take k segs | k <- [1 .. length segs]]
    -- The rest of a name through the namespace of an owner: checked where the members are known.
    navigate owner = \case
      [] -> pure (Canonical (toQName owner))
      s : more -> case namespaceMembers cx sc owner of
        Just members -> case Map.lookup s members of
          Just g -> navigate g more
          Nothing -> Left (ScopeError sp ("no " <> T.unpack (segmentText s) <> " in " <> T.unpack (displayQualName owner)))
        Nothing -> pure (Canonical (toQName (owner <> (s : more))))

-- | A name rewritten to its canonical form, or kept.
rename :: Ctx -> Scope -> Locals -> Span -> QName -> RM QName
rename cx sc locals sp q =
  resolveName cx sc locals sp q <&> \case
    Canonical q' -> q'
    Unchanged -> q
  where
    (<&>) = flip fmap

-- | Operators associated by the fixities in force; an error of theirs is a scope error.
assoc :: Ctx -> Located Expr -> RM (Located Expr)
assoc cx = first (uncurry ScopeError . renderFixityError) . resolveExpr (cxFx cx)

-- * Expressions

renameExpr :: Ctx -> Scope -> Locals -> Located Expr -> RM (Located Expr)
renameExpr cx sc = go
  where
    go locals (Located sp e) =
      Located sp <$> case e of
        EName q -> EName <$> rename cx sc locals sp q
        EApp f x -> EApp <$> go locals f <*> go locals x
        EImplicitApp f x -> EImplicitApp <$> go locals f <*> go locals x
        EOps elems -> EOps <$> traverse (element locals) elems
        EInfix op l r -> EInfix <$> operator locals op <*> go locals l <*> go locals r
        ENot x -> ENot <$> go locals x
        EParen x -> EParen <$> go locals x
        ETuple xs -> ETuple <$> traverse (go locals) xs
        ELam ns body -> ELam ns <$> go (bind (map unLocated ns) locals) body
        ECase s alts -> ECase <$> go locals s <*> traverse (alt locals) alts
        EIf c t f -> EIf <$> go locals c <*> go locals t <*> go locals f
        EPi b body -> do
          (b', locals') <- binder locals b
          EPi b' <$> go locals' body
        EArrow a b -> EArrow <$> go locals a <*> go locals b
        EQuant qu bs bound body -> do
          (bs', locals') <- foldM (\(acc, ls) b -> (\(b', ls') -> (acc <> [b'], ls')) <$> binder ls b) ([], locals) bs
          bound' <- traverse (\(op, t) -> (op,) <$> go locals t) bound
          EQuant qu bs' bound' <$> go locals' body
        EProof rhs -> EProof . unLocated <$> renameRhs cx sc locals (Located sp rhs)
        EConstrained cs body -> EConstrained <$> traverse (constraint locals) cs <*> go locals body
        other -> pure other
    operator locals (Located osp (Operator q bq)) = (\q' -> Located osp (Operator q' bq)) <$> rename cx sc locals osp q
    element locals = \case
      Operand x -> Operand <$> go locals x
      InfixOp op -> InfixOp <$> operator locals op
      n -> pure n
    alt locals (Located asp (Alt p body)) = do
      (p', bs) <- renamePattern cx sc p
      Located asp . Alt p' <$> go (bind bs locals) body
    binder locals (Binder imp ns mt) = do
      mt' <- traverse (go locals) mt
      pure (Binder imp ns mt', bind (map unLocated ns) locals)
    constraint locals (Located csp c, v) = (\c' -> (Located csp c', v)) <$> rename cx sc locals csp c

bind :: [Text] -> Locals -> Locals
bind ns = Set.union (Set.fromList ns)

-- | An expression associated, then renamed.
expression :: Ctx -> Scope -> Locals -> Located Expr -> RM (Located Expr)
expression cx sc locals e = assoc cx e >>= renameExpr cx sc locals

{- |
A pattern: its constructors resolved, and the variables it binds.  A bare
name is a constructor when scope gives it one, or when a data type in scope
has a constructor of that name, to be found by the type expected; otherwise
it is a variable.
-}
renamePattern :: Ctx -> Scope -> Located Expr -> RM (Located Expr, [Text])
renamePattern cx sc = go
  where
    go (Located sp e) = case e of
      EParen x -> first (Located sp . EParen) <$> go x
      EName (QName [] (Ident x))
        | builtin (Ident x) -> pure (Located sp e, [])
        | otherwise -> ctorOrVar sp x
      EName q -> (\q' -> (Located sp (EName q'), [])) <$> rename cx sc Set.empty sp q
      EApp f x -> do
        (f', b1) <- go f
        (x', b2) <- go x
        pure (Located sp (EApp f' x'), b1 <> b2)
      EImplicitApp f x -> do
        (f', b1) <- go f
        (x', b2) <- go x
        pure (Located sp (EImplicitApp f' x'), b1 <> b2)
      EInfix (Located osp (Operator q bq)) l r -> do
        q' <- rename cx sc Set.empty osp q
        (l', b1) <- go l
        (r', b2) <- go r
        pure (Located sp (EInfix (Located osp (Operator q' bq)) l' r'), b1 <> b2)
      _ -> pure (Located sp e, [])
    ctorOrVar sp x =
      let bare = Located sp (EName (QName [] (Ident x)))
       in case lookupBare sc (Ident x) of
            [g] | isCtorQual cx sc g -> pure (Located sp (EName (toQName g)), [])
            gs
              | not (null gs) && all (isCtorQual cx sc) gs -> pure (bare, [])
              | isCtorName cx sc (Ident x) -> pure (bare, [])
              | otherwise -> pure (bare, [x])

-- | The left side of a clause: its head kept as written, which names what the clause defines, and its patterns.
renameLhs :: Ctx -> Scope -> Located Expr -> RM (Located Expr, [Text])
renameLhs cx sc = go
  where
    go (Located sp e) = case e of
      EApp f x -> do
        (f', b1) <- go f
        (x', b2) <- renamePattern cx sc x
        pure (Located sp (EApp f' x'), b1 <> b2)
      EImplicitApp f x -> do
        (f', b1) <- go f
        (x', b2) <- renamePattern cx sc x
        pure (Located sp (EImplicitApp f' x'), b1 <> b2)
      EInfix op l r -> do
        (l', b1) <- renamePattern cx sc l
        (r', b2) <- renamePattern cx sc r
        pure (Located sp (EInfix op l' r'), b1 <> b2)
      EParen x -> first (Located sp . EParen) <$> go x
      _ -> pure (Located sp e, [])

renameClause :: Ctx -> Scope -> Clause -> RM Clause
renameClause cx sc (Clause lhs0 rhs) = do
  lhs <- assoc cx lhs0
  (lhs', bs) <- renameLhs cx sc lhs
  Clause lhs' <$> renameRhs cx sc (Set.fromList bs) rhs

-- * Proofs

renameRhs :: Ctx -> Scope -> Locals -> Located Rhs -> RM (Located Rhs)
renameRhs cx sc locals (Located sp r) =
  Located sp <$> case r of
    RBy ts -> RBy <$> renameTactics cx sc locals ts
    RCalc c -> RCalc <$> renameCalc cx sc locals c
    RExpr e -> RExpr <$> expression cx sc locals e
    RAbsurd -> pure RAbsurd

renameCalc :: Ctx -> Scope -> Locals -> Calc -> RM Calc
renameCalc cx sc locals (Calc first' steps) = Calc <$> expression cx sc locals first' <*> traverse step steps
  where
    step (Located ssp (CalcStep rel t p)) = Located ssp <$> (CalcStep rel <$> expression cx sc locals t <*> traverse (renameRhs cx sc locals) p)

-- | The tactics of a block, in order, each in the scope of the names those before it introduce.
renameTactics :: Ctx -> Scope -> Locals -> [Located Tactic] -> RM [Located Tactic]
renameTactics cx sc = go
  where
    go _ [] = pure []
    go locals (t : ts) = do
      (t', locals') <- renameTactic cx sc locals t
      (t' :) <$> go locals' ts

-- | A tactic renamed, and the scope after it: the names it introduces added.
renameTactic :: Ctx -> Scope -> Locals -> Located Tactic -> RM (Located Tactic, Locals)
renameTactic cx sc locals (Located sp t) =
  first (Located sp) <$> case t of
    TIntro ns -> pure (t, names ns)
    TIntros ns -> pure (t, names ns)
    TExact e -> keep . TExact <$> expr e
    TApply e -> keep . TApply <$> expr e
    TTrans e -> keep . TTrans <$> expr e
    TAbsurd e -> keep . TAbsurd <$> expr e
    TShow e -> keep . TShow <$> expr e
    TTerm e -> keep . TTerm <$> expr e
    TCong (Just e) -> keep . TCong . Just <$> expr e
    TRewrite rules loc -> keep . (`TRewrite` loc) <$> traverse rule rules
    TSimpOnly rules loc -> keep . (`TSimpOnly` loc) <$> traverse rule rules
    TUnfold qs loc -> keep . (`TUnfold` loc) <$> traverse (\(Located qsp q) -> Located qsp <$> rename cx sc locals qsp q) qs
    TCases e arms -> keep <$> (TCases <$> expr e <*> traverse (traverse arm) arms)
    TInduction v gen arms -> keep . TInduction v gen <$> traverse (traverse arm) arms
    TObtain ns e -> (\e' -> (TObtain ns e', names ns)) <$> expr e
    TExists es -> keep . TExists <$> traverse expr es
    THave name ty rhs -> (\ty' rhs' -> (THave name ty' rhs', maybe locals (\n -> bind [unLocated n] locals) name)) <$> traverse expr ty <*> renameRhs cx sc locals rhs
    TCalc c -> keep . TCalc <$> renameCalc cx sc locals c
    TByCases h e -> (\e' -> (TByCases h e', bind [unLocated h] locals)) <$> expr e
    TTry u -> nested TTry u
    TRepeat u -> nested TRepeat u
    TAllGoals u -> nested TAllGoals u
    TAnyGoals u -> nested TAnyGoals u
    TFirst us -> keep . TFirst <$> traverse (fmap fst . renameTactic cx sc locals) us
    TThenAll u v -> do
      (u', locals') <- renameTactic cx sc locals u
      (v', locals'') <- renameTactic cx sc locals' v
      pure (TThenAll u' v', locals'')
    TFocus ts -> keep . TFocus <$> renameTactics cx sc locals ts
    TCase c ns ts -> keep . TCase c ns <$> renameTactics cx sc (names ns) ts
    _ -> pure (t, locals)
  where
    keep x = (x, locals)
    names ns = bind (map unLocated ns) locals
    expr = expression cx sc locals
    rule (RewriteRule back e) = RewriteRule back <$> expr e
    arm (Located asp (Arm c ns body)) = Located asp . Arm c ns <$> renameTactics cx sc (names ns) body
    nested f u = first f <$> renameTactic cx sc locals u

-- * Declarations

-- | A kind: the types and values of the indices it mentions.
renameKind :: Ctx -> Scope -> Locals -> Kind -> RM Kind
renameKind cx sc locals = \case
  KType -> pure KType
  KValue e -> KValue <$> expression cx sc locals e
  KArrow a b -> KArrow <$> renameKind cx sc locals a <*> renameKind cx sc locals b

{- |
The declarations of one module, those under @private@ flattened into them
with their privacy: its data types declared first, so that they may refer
to one another; then each declaration in order, in scope for those after
it.  The scope after, with the module's exports, and the declarations
renamed, nested modules' among them.
-}
renameLevel :: Ctx -> Scope -> [Located Decl] -> (Scope, [RDecl])
renameLevel cx sc0 decls0 = let (sc1, out) = foldl step (predeclared, []) flat in (sc1 {scPrivate = scPrivate sc0}, reverse out)
  where
    flat = flatten (scPrivate sc0) decls0
    flatten p = concatMap \d@(Located _ decl) -> case decl of
      DPrivate inner -> flatten True inner
      _ -> [(p, d)]
    predeclared = foldl predeclare sc0 [(p, d) | (p, Located _ (DData d)) <- flat]
    predeclare sc (p, d) =
      let name = Ident (unLocated (dataName d))
          q = scModule sc <> [name]
          ctors = map (unLocated . constructorName . unLocated) (dataConstructors d) <> map (unLocated . fst) (dataSignatures d)
       in (namespace q (Map.fromList [(c, q <> [c]) | c <- ctors]) (declare name q sc {scPrivate = p}))
            { scCtors = Set.union (Set.fromList ctors) (scCtors sc)
            , scCtorQuals = Set.union (Set.fromList [q <> [c] | c <- ctors]) (scCtorQuals sc)
            , scPrivate = scPrivate sc
            }
    signed = [n | (_, Located _ (DSignature (Located _ n) _)) <- flat]
    headSeg c = either (const Nothing) Just (resolveExpr (cxFx cx) (clauseLhs c)) >>= fmap fst . lhsParts
    clausesOf name = [c | (_, Located _ (DClause c)) <- flat, headSeg c == Just name]
    owner sc d = RDecl (scModule sc) d

    step (sc, out) (p, Located sp d) =
      let sc' = sc {scPrivate = p}
          emit s ds = (s, reverse (map (owner s) ds) <> out)
       in case d of
            DOpen lq dirs public -> case namespaceOf cx sc' lq of
              Left err -> (failed err sc', out)
              Right (own, members) -> case applyDirectives dirs members of
                Left err -> (failed err sc', out)
                Right view -> (openView own view public sc', out)
            DImport imp -> either (\err -> (failed err sc', out)) (,out) (importInto cx sc' imp)
            DOpenImport imp public -> case importInto cx sc' imp of
              Left err -> (failed err sc', out)
              Right sc'' -> case Map.lookup (importedAs imp) (scImports sc'') of
                Just view -> (openView (importedAs imp) view public sc'', out)
                Nothing -> (failed (ScopeError sp "internal: the module imported is not in scope") sc'', out)
            DModule (Located _ name) inner ->
              let entered = sc' {scModule = scModule sc' <> [Ident name], scExports = Map.empty, scPrivate = False}
                  (scInner, ds) = renameLevel cx entered inner
                  q = scModule entered
                  left =
                    scInner
                      { scModule = scModule sc'
                      , scTop = scTop sc'
                      , scExports = scExports sc'
                      , scPrivate = p
                      , scOpened = scOpened sc'
                      , scImports = scImports sc'
                      , scModules = (q, scExports scInner) : scModules scInner
                      }
               in (namespace q (scExports scInner) (declare (Ident name) q left), reverse ds <> out)
            DPrivate _ -> (sc', out)
            DData dd -> case renameData cx sc' dd of
              Left err -> (failed err sc', out)
              Right dd' -> emit sc' [Located sp (DData dd')]
            DKindSig n k -> case renameKind cx sc' Set.empty k of
              Left err -> (failed err sc', out)
              Right k' -> emit sc' [Located sp (DKindSig n k')]
            DFixity {} -> emit sc' [Located sp d]
            DSignature (Located nsp name) ty ->
              let declared = declare name (scModule sc' <> [name]) sc'
                  renamed = do
                    ty' <- expression cx declared Set.empty ty
                    clauses <- forM (clausesOf name) (renameClause cx declared)
                    pure (Located sp (DSignature (Located nsp name) ty') : [Located (spanning (location (clauseLhs c)) (location (clauseRhs c))) (DClause c) | c <- clauses])
               in either (\err -> (failed err declared, out)) (emit declared) renamed
            DClause c
              | headSeg c `elem` map Just signed -> (sc', out)
              | otherwise -> emit sc' [Located sp d]
            DClass cd -> case renameClass cx sc' cd of
              Left err -> (failed err sc', out)
              Right (cd', sc'') -> emit sc'' [Located sp (DClass cd')]
            DInstance idl -> case renameInstance cx sc' idl of
              Left err -> (failed err sc', out)
              Right (idl', sc'') -> emit sc'' [Located sp (DInstance idl')]

-- | A data type: the kinds of its parameters and its own, and the types of its constructors' fields, over its parameters.
renameData :: Ctx -> Scope -> DataDecl -> RM DataDecl
renameData cx sc d = do
  let locals = Set.fromList (map (unLocated . dataParamName) (dataParams d))
  params <- forM (dataParams d) \p -> (\k -> p {dataParamKind = k}) <$> traverse (renameKind cx sc locals) (dataParamKind p)
  kind <- traverse (renameKind cx sc locals) (dataKind d)
  ctors <- forM (dataConstructors d) \(Located csp (Constructor n fields)) -> Located csp . Constructor n <$> traverse (expression cx sc locals) fields
  sigs <- forM (dataSignatures d) \(n, ty) -> (n,) <$> expression cx sc locals ty
  pure d {dataParams = params, dataKind = kind, dataConstructors = ctors, dataSignatures = sigs}

-- | A class: its superclasses resolved, the types of its members over its parameter; it declares its name, its methods and its laws, and is a namespace of them.
renameClass :: Ctx -> Scope -> ClassDecl -> RM (ClassDecl, Scope)
renameClass cx sc cd = do
  let locals = Set.singleton (unLocated (classParam cd))
      name = Ident (unLocated (className cd))
      q = scModule sc <> [name]
      memberNames = map (unLocated . fst) (classMembers cd)
      -- The class, its methods and its laws are in scope in the members' types: a law mentions the methods.
      sc' = foldr (\m -> declare m (q <> [m])) (namespace q (Map.fromList [(m, q <> [m]) | m <- memberNames]) (declare name q sc)) memberNames
  supers <- forM (classSupers cd) \(Located csp c, v) -> (\c' -> (Located csp c', v)) <$> rename cx sc Set.empty csp c
  members <- forM (classMembers cd) \(m, ty) -> (m,) <$> expression cx sc' locals ty
  pure (cd {classSupers = supers, classMembers = members}, sc')

{- |
An instance: its class and its context resolved, its type, and its clauses;
it declares its name, @C-T@ unless given, and is a namespace of the
functions of its methods and the theorems of its laws.
-}
renameInstance :: Ctx -> Scope -> InstanceDecl -> RM (InstanceDecl, Scope)
renameInstance cx sc idl = do
  let Located csp cq = instanceClass idl
  cls <- rename cx sc Set.empty csp cq
  context <- forM (instanceContext idl) \(Located ksp c, v) -> (\c' -> (Located ksp c', v)) <$> rename cx sc Set.empty ksp c
  ty <- expression cx sc Set.empty (instanceType idl)
  let shortHead = case rawSpine ty of
        (Located _ (EName (QName _ b)), _)
          | b `elem` [Ident "Nat", Ident "nat"] -> "Nat"
          | otherwise -> segmentText b
        _ -> "?"
      name = Ident (maybe (segmentText (qnameBase cls) <> "-" <> shortHead) unLocated (instanceName idl))
      iq = scModule sc <> [name]
      classMembers' = fromMaybe Map.empty (namespaceMembers cx sc (qnameSegments cls))
      sc' = namespace iq (Map.fromList [(m, iq <> [m]) | m <- Map.keys classMembers']) (declare name iq sc)
  clauses <- forM (instanceClauses idl) \(Located clsp c) -> Located clsp <$> renameClause cx sc' c
  pure (idl {instanceClass = Located csp cls, instanceContext = context, instanceType = ty, instanceClauses = clauses}, sc')

-- * Imports and openings

-- | The name an import is in scope by: the one after @as@, or the module's.
importedAs :: Import -> QualName
importedAs imp = qnameSegments (unLocated (fromMaybe (importModule imp) (importAs imp)))

-- | An import: the module's exports, as the build resolved them, taken by its directives, in scope by its name or its alias.
importInto :: Ctx -> Scope -> Import -> RM Scope
importInto cx sc imp@(Import lib (Located msp mq) _ dirs) =
  case Map.lookup (unLocated <$> lib, qnameSegments mq) (cxImports cx) of
    Nothing -> Left (ScopeError msp ("no module " <> T.unpack (qnameText mq) <> " to import: the file is checked on its own, outside a package"))
    Just (Left why) -> Left (ScopeError msp why)
    Just (Right exports) -> do
      view <- applyDirectives dirs (meMembers exports)
      pure sc {scImports = Map.insert (importedAs imp) view (scImports sc)}

-- | Open a view of a namespace: its members in unqualified scope, and exported when public.
openView :: QualName -> Map Segment QualName -> Bool -> Scope -> Scope
openView own view public sc =
  sc
    { scOpened = scOpened sc <> [(own, view)]
    , scExports = if public then Map.union (scExports sc) view else scExports sc
    }

{- |
The namespace a name after @open@ refers to, with its members: an imported
module by the name it is in scope by, or a global whose members are known —
a module, a data type, a class, an instance.
-}
namespaceOf :: Ctx -> Scope -> Located QName -> RM (QualName, Map Segment QualName)
namespaceOf cx sc (Located sp q) = case Map.lookup (qnameSegments q) (scImports sc) of
  Just view -> pure (qnameSegments q, view)
  Nothing ->
    resolveName cx sc Set.empty sp q >>= \case
      Canonical q' -> case namespaceMembers cx sc (qnameSegments q') of
        Just members -> pure (qnameSegments q', members)
        Nothing -> Left (ScopeError sp ("not a namespace to open: " <> T.unpack (qnameText q) <> "; a module, a data type, a class or an instance is"))
      Unchanged -> Left (ScopeError sp ("no namespace " <> T.unpack (qnameText q) <> " to open"))

{- |
The view of a namespace an import or an opening takes: the members named
after @using@ and no other, when it is given; none of those after
@hiding@; and each renamed by its new name.  A name none of the members
has is refused, where it is written.
-}
applyDirectives :: Directives -> Map Segment QualName -> RM (Map Segment QualName)
applyDirectives (Directives using hiding renaming) members = do
  forM_ (fromMaybe [] using <> hiding <> map fst renaming) \(Located sp s) ->
    unless (Map.member s members) $ Left (ScopeError sp ("no member " <> T.unpack (segmentText s) <> " to take or leave: the members are " <> T.unpack (T.unwords (map segmentText (Map.keys members)))))
  let kept = maybe members (\us -> Map.restrictKeys members (Set.fromList (map unLocated us))) using
      unhidden = Map.withoutKeys kept (Set.fromList (map unLocated hiding <> map (unLocated . fst) renaming))
      renamed = Map.fromList [(to, members Map.! from) | (Located _ from, Located _ to) <- renaming]
  pure (Map.union renamed unhidden)
