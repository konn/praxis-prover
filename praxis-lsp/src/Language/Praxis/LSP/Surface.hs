{-# LANGUAGE OverloadedStrings #-}

{- |
The index of a module of the surface language: what each name in it is,
and where what it names is declared.

The module is read as the renamer left it, "Language.Praxis.Surface.Rename":
every global by its canonical name, which the environment after
elaboration, "Language.Praxis.Surface.Env", tells the kind of — a data type,
a constructor, a function, a theorem, a class, a method, an instance, a
module.  The names the renamer leaves as written are the locals, followed
through the binders as the renamer follows them; the builtins; the
constructors found by their bare names among the modules in scope; the
lemmas of the library; and, in a type, the type variables and the value
parameters a signature binds implicitly.  The words of the tactics, which are
words only in tactic position, are read from the source at the position of
each tactic.
-}
module Language.Praxis.LSP.Surface (
  moduleDefinitions,
  indexModule,
  tacticWords,
) where

import Data.Char (isAlphaNum, isSpace)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Protocol.Types (SemanticTokenModifiers (..), SemanticTokenTypes (..))
import Language.Praxis.LSP.Index
import Language.Praxis.LSP.Position (Lines, charToColumn, columnToChar, lineAt)
import Language.Praxis.Surface.Env (CtorInfo (..), Env, Global (..), QualName, constructorsNamed, explicitPositions, resolve)
import Language.Praxis.Surface.Fixity (isRelation)
import Language.Praxis.Surface.Rename (RDecl (..), Renamed (..))
import Language.Praxis.Surface.Shape (opText, rawArgs)
import Language.Praxis.Surface.Syntax.Raw

-- * Definitions

{- |
Where every global a module declares is declared: the module and the
modules nested in it at their headers, a data type, a function, a theorem,
a class or an instance at its name, a constructor and a method at theirs,
and the function of an instance's method at its first clause.
-}
moduleDefinitions :: FilePath -> Renamed -> Definitions
moduleDefinitions path rn = Map.fromListWith (\_ old -> old) (headers <> concatMap decl (rnDecls rn))
  where
    at = Target path
    headers = [(q, at sp) | (sp, q) <- rnHeaders rn]
    decl (RDecl owner (Located _ d)) = case d of
      DSignature (Located sp n) _ -> [(owner <> [n], at sp)]
      DData dd ->
        let q = owner <> [Ident (unLocated (dataName dd))]
         in (q, at (location (dataName dd)))
              : [(q <> [n], at sp) | Located sp n <- map (constructorName . unLocated) (dataConstructors dd) <> map fst (dataSignatures dd)]
      DClass cd ->
        let q = owner <> [Ident (unLocated (className cd))]
         in (q, at (location (className cd))) : [(q <> [n], at sp) | (Located sp n, _) <- classMembers cd]
      DInstance idl
        | Just (Located sp n) <- instanceName idl ->
            let q = owner <> [Ident n]
             in (q, at sp) : [(q <> [h], at hsp) | Located _ (Clause lhs _) <- instanceClauses idl, Just (Located hsp h) <- [clauseHead lhs]]
      _ -> []

-- | The name a clause defines, where it is written: the head of its left side.
clauseHead :: Located Expr -> Maybe (Located Segment)
clauseHead (Located sp e) = case e of
  EApp f _ -> clauseHead f
  EImplicitApp f _ -> clauseHead f
  EParen x -> clauseHead x
  EName (QName [] s) -> Just (Located sp s)
  EInfix (Located osp op) _ _ | QName [] s <- operatorName op -> Just (Located osp s)
  _ -> Nothing

-- * The index

-- | What a name stands for where it is written: in a type, a type; at an index of a type, or on a side of a relation in one, a value; in a term or a proof, a term.
data Mode = TypeMode | ValueMode | TermMode
  deriving stock (Eq)

-- | The names bound around a position, each with the kind of token its occurrences are.
type Locals = Map Text SemanticTokenTypes

data Cx = Cx
  { cxLines :: !Lines
  , cxEnv :: !Env
  , cxLibrary :: !(Set Text)
  , cxDefs :: !Definitions
  , cxImplicits :: !(Map QualName [SemanticTokenTypes])
  -- ^ for each signature, what the implicit binders in front of it bind, in order: what a clause's patterns in braces stand for
  }

{- |
The index of a module: from its source, its syntax as parsed, as renamed,
the environment after its elaboration, the names of the lemmas of the
library, and where every global known is declared.
-}
indexModule :: Lines -> Module -> Renamed -> Env -> Set Text -> Definitions -> Index
indexModule ls raw rn env library defs = Index (normalizeTokens tokens) refs
  where
    cx = Cx ls env library defs implicits
    implicits = Map.fromList [(owner <> [n], implicitKinds ty) | RDecl owner (Located _ (DSignature (Located _ n) ty)) <- rnDecls rn]
    Index tokens refs =
      foldMap (\(sp, _) -> token sp SemanticTokenTypes_Namespace [SemanticTokenModifiers_Declaration]) (rnHeaders rn)
        <> foldMap (resolvedName cx) (rnResolved rn)
        <> foldMap (importWords cx) (allDecls (moduleDecls raw))
        <> foldMap (declIndex cx) (rnDecls rn)

-- | Every declaration of a file, those of its nested modules and private blocks among them.
allDecls :: [Located Decl] -> [Located Decl]
allDecls = concatMap \d@(Located _ decl) ->
  d : case decl of
    DModule _ ds -> allDecls ds
    DPrivate ds -> allDecls ds
    _ -> []

-- * Globals

segments :: QName -> QualName
segments (QName qs b) = qs <> [b]

-- | The global a canonical name refers to, when the environment knows it.
global :: Env -> QualName -> Maybe Global
global env q = case q of
  _ : _ : _ -> case resolve env (QName (init q) (last q)) of
    g : _ -> Just g
    [] -> Nothing
  _ -> Nothing

globalKind :: Global -> (SemanticTokenTypes, [SemanticTokenModifiers])
globalKind = \case
  GData _ -> (SemanticTokenTypes_Type, [])
  GCtor _ -> (SemanticTokenTypes_EnumMember, [])
  GFun _ -> (SemanticTokenTypes_Function, [])
  GTheorem _ -> (SemanticTokenTypes_Function, [])
  GClass _ -> (SemanticTokenTypes_Class, [])
  GMethod _ -> (SemanticTokenTypes_Method, [])
  GLaw _ -> (SemanticTokenTypes_Method, [])
  GInstance _ -> (SemanticTokenTypes_Namespace, [])
  GModule _ -> (SemanticTokenTypes_Namespace, [])

-- | The kind of token a canonical name is: that of its global, or, for a lemma generated for a function, a function's.
kindOf :: Env -> QualName -> Maybe (SemanticTokenTypes, [SemanticTokenModifiers])
kindOf env q = case global env q of
  Just g -> Just (globalKind g)
  Nothing
    | length q > 1, Just (GFun _) <- global env (init q) -> Just (SemanticTokenTypes_Function, [])
    | otherwise -> Nothing

-- | Where a canonical name is declared: the global, or, for a lemma generated for a function, the function.
definitionsOf :: Cx -> QualName -> [Target]
definitionsOf cx q = case Map.lookup q (cxDefs cx) of
  Just t -> [t]
  Nothing
    | length q > 1, Just (GFun _) <- global (cxEnv cx) (init q) -> maybe [] pure (Map.lookup (init q) (cxDefs cx))
    | otherwise -> []

-- | A reference to a global by its canonical name: its token, and its definition.
refer :: Cx -> Span -> QualName -> Index
refer cx sp q = maybe mempty (\(t, ms) -> token sp t ms) (kindOf (cxEnv cx) q) <> reference sp (definitionsOf cx q)

-- | A name an import, an opening or a directive wrote, resolved: a module when the environment knows no other global of the name.
resolvedName :: Cx -> (Span, QualName) -> Index
resolvedName cx (sp, q) = maybe (token sp SemanticTokenTypes_Namespace []) (\(t, ms) -> token sp t ms) (kindOf (cxEnv cx) q) <> reference sp (definitionsOf cx q)

-- | A constructor by its bare name: every constructor of that name among the modules in scope.
bareConstructor :: Cx -> Span -> Segment -> Maybe Index
bareConstructor cx sp s = case constructorsNamed (cxEnv cx) s of
  [] -> Nothing
  cs -> Just (token sp SemanticTokenTypes_EnumMember [] <> reference sp (concatMap (definitionsOf cx . ctorQual) cs))

-- | The names never resolved to a global: the successor, the words of proof terms, and the type of numbers.
builtin :: Span -> Segment -> Maybe Index
builtin sp = \case
  Ident x
    | x `elem` ["S", "suc", "absurd", "rfl", "refl", "cong"] -> Just (token sp SemanticTokenTypes_Function [SemanticTokenModifiers_DefaultLibrary])
    | x `elem` ["Nat", "nat"] -> Just (token sp SemanticTokenTypes_Type [SemanticTokenModifiers_DefaultLibrary])
  _ -> Nothing

-- | A hypothesis the engine names itself: @IH@, @IH1@, ….
implicitHypothesis :: Text -> Bool
implicitHypothesis x = x == "IH" || ("IH" `T.isPrefixOf` x && T.length x > 2 && T.all (`elem` ['0' .. '9']) (T.drop 2 x))

{- |
A name where it is written.  Unqualified, it is a local, an implicit
hypothesis, a builtin, a constructor by its bare name, a lemma of the
library, or, in a type, a type variable, and at an index or on a side of a
relation, a value parameter.  Qualified, it is canonical, and each of its
segments as written names a prefix of it.
-}
name :: Cx -> Mode -> Locals -> Span -> QName -> Index
name cx mode locals sp = \case
  QName [] s -> case s of
    Ident x
      | Just t <- Map.lookup x locals -> token sp t []
      | implicitHypothesis x -> token sp SemanticTokenTypes_Variable []
    _
      | Just ix <- builtin sp s -> ix
      | Just ix <- bareConstructor cx sp s -> ix
    Ident x
      | Set.member x (cxLibrary cx) -> token sp SemanticTokenTypes_Function [SemanticTokenModifiers_DefaultLibrary]
      | mode == TypeMode -> token sp SemanticTokenTypes_TypeParameter []
      | mode == ValueMode -> token sp SemanticTokenTypes_Parameter []
    _ -> mempty
  q -> qualified cx sp (segments q)

-- | A qualified name, canonical, by the segments written: the last @n@ segments of the canonical name are those written, in order.
qualified :: Cx -> Span -> QualName -> Index
qualified cx sp full = case segmentSpans (cxLines cx) sp of
  written
    | not (null written)
    , length full >= length written ->
        let m = length full
            n = length written
         in mconcat [refer cx ssp (take (m - n + i) full) | (i, ssp) <- zip [1 ..] written]
  _ -> refer cx sp full

-- | The spans of the segments of a qualified name as written: separated by dots outside parentheses.
segmentSpans :: Lines -> Span -> [Span]
segmentSpans ls (Span (l, c) (l', c'))
  | l /= l' = []
  | otherwise =
      let line = lineAt ls l
          from = columnToChar line c
          to = columnToChar line c'
          text = T.take (to - from) (T.drop from line)
       in [Span (l, c + a) (l, c + b) | (a, b) <- splitSegments text]

splitSegments :: Text -> [(Int, Int)]
splitSegments t = go 0 0 (0 :: Int) (T.unpack t) []
  where
    go start i depth cs acc = case cs of
      [] -> reverse ((start, i) : acc)
      '(' : rest -> go start (i + 1) (depth + 1) rest acc
      ')' : rest -> go start (i + 1) (max 0 (depth - 1)) rest acc
      '.' : rest | depth == 0 -> go (i + 1) (i + 1) depth rest ((start, i) : acc)
      _ : rest -> go start (i + 1) depth rest acc

-- * Expressions

declareAll :: SemanticTokenTypes -> [Located Text] -> Index
declareAll t = foldMap \(Located sp _) -> token sp t [SemanticTokenModifiers_Declaration]

bindAll :: SemanticTokenTypes -> [Located Text] -> Locals -> Locals
bindAll t ns locals = foldr (\(Located _ n) -> Map.insert n t) locals ns

-- | The span of a name between backquotes, without them.
unquoted :: Span -> Span
unquoted (Span (l, c) (l', c')) = Span (l, c + 1) (l', max (c + 1) (c' - 1))

{- |
An operator between operands: a name in backquotes as the name is, and a
symbol a reference to what it names, its token left to the grammar of the
editor.
-}
operator :: Cx -> Locals -> Located Operator -> Index
operator cx locals (Located osp (Operator q backquoted))
  | backquoted = name cx TermMode locals (unquoted osp) q
  | otherwise = case q of
      QName [] s -> reference osp (concatMap (definitionsOf cx . ctorQual) (constructorsNamed (cxEnv cx) s))
      _ -> reference osp (definitionsOf cx (segments q))

-- | What the operands of an operator are, in a type: values on the sides of a relation and under arithmetic, types otherwise.
operandMode :: Mode -> Located Operator -> Mode
operandMode mode op = case mode of
  TypeMode
    | isRelation o || o `elem` ["+", "-", "*", "^"] -> ValueMode
    | otherwise -> TypeMode
  m -> m
  where
    o = opText op

expr :: Cx -> Mode -> Locals -> Located Expr -> Index
expr cx mode locals le@(Located sp e) = case e of
  EName q -> name cx mode locals sp q
  ENat _ -> mempty
  EWildcard -> mempty
  EAbsurd -> mempty
  EType -> mempty
  EApp {} -> application cx mode locals le
  EImplicitApp {} -> application cx mode locals le
  EOps elems -> foldMap element elems
  EInfix op l r -> let m = operandMode mode op in operator cx locals op <> expr cx m locals l <> expr cx m locals r
  ENot x -> expr cx mode locals x
  EParen x -> expr cx mode locals x
  ETuple xs -> foldMap (expr cx mode locals) xs
  ELam ns body -> declareAll SemanticTokenTypes_Parameter ns <> expr cx TermMode (bindAll SemanticTokenTypes_Parameter ns locals) body
  ECase s alts -> expr cx mode locals s <> foldMap alt alts
  EIf c t f -> foldMap (expr cx mode locals) [c, t, f]
  EPi b body -> let (ix, locals') = binder cx locals b in ix <> expr cx mode locals' body
  EArrow a b -> expr cx mode locals a <> expr cx mode locals b
  EQuant _ bs bound body ->
    let (ix, locals') = foldl (\(acc, ls) b -> let (ix', ls') = binder cx ls b in (acc <> ix', ls')) (mempty, locals) bs
        boundMode = if mode == TermMode then TermMode else ValueMode
     in ix <> maybe mempty (\(_, t) -> expr cx boundMode locals t) bound <> expr cx mode locals' body
  EProof rhs -> rhsIndex cx locals rhs
  EConstrained cs body -> foldMap (constraint cx) cs <> expr cx mode locals body
  where
    element = \case
      Operand x -> expr cx mode locals x
      InfixOp op -> operator cx locals op
      PrefixNot _ -> mempty
    alt (Located _ (Alt p body)) = let (ix, locals') = pattern cx locals p in ix <> expr cx mode locals' body

{- |
An application: in a type, the arguments of a data type are types at its
type parameters and values at its indices; elsewhere they are what the
application is.
-}
application :: Cx -> Mode -> Locals -> Located Expr -> Index
application cx mode locals le =
  let (h, args) = rawArgs le
      explicitModes = case (mode, unLocated h) of
        (TypeMode, EName q) | Just (GData d) <- global (cxEnv cx) (segments q) -> replicate (length (fst (explicitPositions d))) TypeMode <> repeat ValueMode
        _ -> repeat mode
      assign ms = \case
        [] -> []
        Left x : rest -> (if mode == TypeMode then TypeMode else mode, x) : assign ms rest
        Right x : rest -> case ms of
          m : ms' -> (m, x) : assign ms' rest
          [] -> (mode, x) : assign [] rest
   in expr cx mode locals h <> mconcat [expr cx m locals a | (m, a) <- assign explicitModes args]

-- | Names bound together: type variables when their type is @Type@, or when implicit and untyped; values otherwise.
binder :: Cx -> Locals -> Binder -> (Index, Locals)
binder cx locals (Binder implicit ns mt) =
  let kind = binderKind implicit mt
   in (declareAll kind ns <> maybe mempty (expr cx TypeMode locals) mt, bindAll kind ns locals)

-- | A constraint on a type variable: the class, and the variable.
constraint :: Cx -> TyConstraint -> Index
constraint cx (Located csp cq, Located vsp _) = qualified cx csp (segments cq) <> token vsp SemanticTokenTypes_TypeParameter []

{- |
A pattern: its constructors, resolved or by their bare names, the
successor, and the variables it binds, which are every other name.
-}
pattern :: Cx -> Locals -> Located Expr -> (Index, Locals)
pattern cx locals (Located sp e) = case e of
  EParen x -> pattern cx locals x
  EName (QName [] s)
    | Just ix <- builtin sp s -> (ix, locals)
    | Just ix <- bareConstructor cx sp s -> (ix, locals)
    | Ident x <- s -> (token sp SemanticTokenTypes_Variable [SemanticTokenModifiers_Declaration], Map.insert x SemanticTokenTypes_Variable locals)
    | otherwise -> (mempty, locals)
  EName q -> (qualified cx sp (segments q), locals)
  EApp f x -> both f x
  EImplicitApp f x -> both f x
  EInfix op l r ->
    let (il, ls1) = pattern cx locals l
        (ir, ls2) = pattern cx ls1 r
     in (operator cx locals op <> il <> ir, ls2)
  ETuple xs -> foldl (\(acc, ls) x -> let (ix, ls') = pattern cx ls x in (acc <> ix, ls')) (mempty, locals) xs
  _ -> (mempty, locals)
  where
    both f x =
      let (i1, ls1) = pattern cx locals f
          (i2, ls2) = pattern cx ls1 x
       in (i1 <> i2, ls2)

-- * Declarations

declIndex :: Cx -> RDecl -> Index
declIndex cx (RDecl owner (Located _ d)) = case d of
  DSignature (Located nsp n) ty -> declared cx nsp (owner <> [n]) <> expr cx TypeMode Map.empty ty
  DClause c -> clauseIndex cx owner c
  DData dd -> dataIndex cx owner dd
  DKindSig (Located ksp n) k -> refer cx ksp (owner <> [Ident n]) <> kindIndex cx Map.empty k
  DClass cd -> classIndex cx owner cd
  DInstance idl -> instanceIndex cx owner idl
  _ -> mempty

-- | The name of a signature: a function, or a theorem, declared.
declared :: Cx -> Span -> QualName -> Index
declared cx sp q = token sp (maybe SemanticTokenTypes_Function fst (kindOf (cxEnv cx) q)) [SemanticTokenModifiers_Declaration]

-- | The head of a clause: the function or theorem it defines, with a reference to its signature.
definedHead :: Cx -> Bool -> Span -> QualName -> Index
definedHead cx withToken sp q =
  (if withToken then token sp (maybe SemanticTokenTypes_Function fst (kindOf (cxEnv cx) q)) [SemanticTokenModifiers_Definition] else mempty)
    <> reference sp (definitionsOf cx q)

-- | What the implicit binders in front of a signature bind, in order: type variables, or values.
implicitKinds :: Located Expr -> [SemanticTokenTypes]
implicitKinds (Located _ e) = case e of
  EPi (Binder True ns mt) body -> map (const (binderKind True mt)) ns <> implicitKinds body
  EConstrained _ body -> implicitKinds body
  _ -> []

-- | What a binder binds: type variables when their type is @Type@, or when implicit and untyped; values otherwise.
binderKind :: Bool -> Maybe (Located Expr) -> SemanticTokenTypes
binderKind implicit = \case
  Just (Located _ EType) -> SemanticTokenTypes_TypeParameter
  Just _ -> SemanticTokenTypes_Parameter
  Nothing -> if implicit then SemanticTokenTypes_TypeParameter else SemanticTokenTypes_Parameter

clauseIndex :: Cx -> QualName -> Clause -> Index
clauseIndex cx owner (Clause lhs (Located _ rhs)) =
  let implicits = maybe [] (\(Located _ h) -> Map.findWithDefault [] (owner <> [h]) (cxImplicits cx)) (clauseHead lhs)
      (ix, (locals, _)) = lhsIndex cx owner (Map.empty, implicits) lhs
   in ix <> rhsIndex cx locals rhs

{- |
The left side of a clause: its head as the name it defines, and its
patterns, those in braces standing for what the signature's implicit
binders bind, in order.
-}
lhsIndex :: Cx -> QualName -> (Locals, [SemanticTokenTypes]) -> Located Expr -> (Index, (Locals, [SemanticTokenTypes]))
lhsIndex cx owner state@(locals, implicits) (Located sp e) = case e of
  EApp f x ->
    let (i1, (ls1, imps1)) = lhsIndex cx owner state f
        (i2, ls2) = pattern cx ls1 x
     in (i1 <> i2, (ls2, imps1))
  EImplicitApp f x ->
    let (i1, (ls1, imps1)) = lhsIndex cx owner state f
        (i2, ls2) = case (imps1, bareName x) of
          (kind : _, Just (nsp, v)) | Nothing <- builtin nsp (Ident v), Nothing <- bareConstructor cx nsp (Ident v) -> (token nsp kind [SemanticTokenModifiers_Declaration], Map.insert v kind ls1)
          _ -> pattern cx ls1 x
     in (i1 <> i2, (ls2, drop 1 imps1))
  EParen x -> lhsIndex cx owner state x
  EInfix (Located osp (Operator q backquoted)) l r
    | QName [] s <- q ->
        let (il, ls1) = pattern cx locals l
            (ir, ls2) = pattern cx ls1 r
         in (definedHead cx backquoted (if backquoted then unquoted osp else osp) (owner <> [s]) <> il <> ir, (ls2, implicits))
  EName (QName [] s) -> (definedHead cx True sp (owner <> [s]), state)
  _ -> (mempty, state)
  where
    bareName (Located nsp x) = case x of
      EParen y -> bareName y
      EName (QName [] (Ident v)) -> Just (nsp, v)
      _ -> Nothing

rhsIndex :: Cx -> Locals -> Rhs -> Index
rhsIndex cx locals = \case
  RBy ts -> tacticsIndex cx locals ts
  RCalc c -> calcIndex cx locals c
  RExpr e -> expr cx TermMode locals e
  RAbsurd -> mempty

calcIndex :: Cx -> Locals -> Calc -> Index
calcIndex cx locals (Calc first' steps) = expr cx TermMode locals first' <> foldMap step steps
  where
    step (Located _ (CalcStep _ t p)) = expr cx TermMode locals t <> maybe mempty (rhsIndex cx locals . unLocated) p

kindIndex :: Cx -> Locals -> Kind -> Index
kindIndex cx locals = \case
  KType -> mempty
  KValue e -> expr cx TypeMode locals e
  KArrow a b -> kindIndex cx locals a <> kindIndex cx locals b

dataIndex :: Cx -> QualName -> DataDecl -> Index
dataIndex cx _ dd =
  token (location (dataName dd)) SemanticTokenTypes_Type [SemanticTokenModifiers_Declaration]
    <> foldMap param (dataParams dd)
    <> maybe mempty (kindIndex cx locals) (dataKind dd)
    <> foldMap ctor (dataConstructors dd)
    <> foldMap sig (dataSignatures dd)
  where
    paramKind p = case dataParamKind p of
      Just KType -> SemanticTokenTypes_TypeParameter
      Just _ -> SemanticTokenTypes_Parameter
      Nothing -> SemanticTokenTypes_TypeParameter
    locals = Map.fromList [(unLocated (dataParamName p), paramKind p) | p <- dataParams dd]
    param p = token (location (dataParamName p)) (paramKind p) [SemanticTokenModifiers_Declaration] <> maybe mempty (kindIndex cx locals) (dataParamKind p)
    ctor (Located _ (Constructor (Located csp _) fields)) = token csp SemanticTokenTypes_EnumMember [SemanticTokenModifiers_Declaration] <> foldMap (expr cx TypeMode locals) fields
    sig (Located csp _, ty) = token csp SemanticTokenTypes_EnumMember [SemanticTokenModifiers_Declaration] <> expr cx TypeMode locals ty

classIndex :: Cx -> QualName -> ClassDecl -> Index
classIndex cx _ cd =
  foldMap (constraint cx) (classSupers cd)
    <> token (location (className cd)) SemanticTokenTypes_Class [SemanticTokenModifiers_Declaration]
    <> token (location (classParam cd)) SemanticTokenTypes_TypeParameter [SemanticTokenModifiers_Declaration]
    <> foldMap member (classMembers cd)
  where
    locals = Map.singleton (unLocated (classParam cd)) SemanticTokenTypes_TypeParameter
    member (Located msp _, ty) = token msp SemanticTokenTypes_Method [SemanticTokenModifiers_Declaration] <> expr cx TypeMode locals ty

-- | An instance: its name when written, its context, its class, its type, and the clauses of its methods, each defining a function of the instance.
instanceIndex :: Cx -> QualName -> InstanceDecl -> Index
instanceIndex cx owner idl =
  maybe mempty named (instanceName idl)
    <> foldMap (constraint cx) (instanceContext idl)
    <> qualified cx csp (segments cq)
    <> expr cx TypeMode Map.empty (instanceType idl)
    <> foldMap (\(Located _ c) -> clauseIndex cx iq c) (instanceClauses idl)
  where
    Located csp cq = instanceClass idl
    iq = owner <> [Ident n | Just (Located _ n) <- [instanceName idl]]
    -- A name the renamer derived stands at the class's position, which is the class's token.
    named (Located nsp _)
      | nsp == csp = mempty
      | otherwise = token nsp SemanticTokenTypes_Namespace [SemanticTokenModifiers_Declaration]

-- * Tactics

-- | The words of the tactic language, keywords in tactic position only.
tacticWords :: Set Text
tacticWords =
  Set.fromList
    [ "intro"
    , "intros"
    , "exact"
    , "apply"
    , "rfl"
    , "refl"
    , "reflexivity"
    , "symm"
    , "symmetry"
    , "trans"
    , "transitivity"
    , "rw"
    , "rewrite"
    , "unfold"
    , "simp"
    , "only"
    , "constructor"
    , "split"
    , "left"
    , "right"
    , "exfalso"
    , "contradiction"
    , "absurd"
    , "assumption"
    , "trivial"
    , "decide"
    , "cong"
    , "congr"
    , "cases"
    , "destruct"
    , "induction"
    , "generalizing"
    , "obtain"
    , "exists"
    , "use"
    , "have"
    , "assert"
    , "show"
    , "change"
    , "calc"
    , "revert"
    , "clear"
    , "by_cases"
    , "sorry"
    , "admit"
    , "try"
    , "repeat"
    , "first"
    , "all_goals"
    , "any_goals"
    , "case"
    , "at"
    ]

tacticsIndex :: Cx -> Locals -> [Located Tactic] -> Index
tacticsIndex cx locals0 = snd . foldl (\(ls, acc) t -> let (ix, ls') = tacticIndex cx ls t in (ls', acc <> ix)) (locals0, mempty)

-- | A tactic: its word, what it mentions, and the scope after it, with the names it introduces.
tacticIndex :: Cx -> Locals -> Located Tactic -> (Index, Locals)
tacticIndex cx locals (Located sp t) = case t of
  TIntro ns -> introduce ns
  TIntros ns -> introduce ns
  TExact e -> plain (term e)
  TApply e -> plain (term e)
  TTrans e -> plain (term e)
  TAbsurd e -> plain (term e)
  TShow e -> plain (term e)
  TTerm e -> (term e, locals)
  TRefl -> plain mempty
  TSymm -> plain mempty
  TConstructor -> plain mempty
  TLeft -> plain mempty
  TRight -> plain mempty
  TExfalso -> plain mempty
  TContradiction -> plain mempty
  TAssumption -> plain mempty
  TTrivial -> plain mempty
  TDecide -> plain mempty
  TSorry -> plain mempty
  TCong me -> plain (maybe mempty term me)
  TRewrite rules loc -> plain (foldMap rule rules <> at loc)
  TSimpOnly rules loc -> plain (secondWord "only" <> foldMap rule rules <> at loc)
  TUnfold qs loc -> plain (foldMap (\(Located qsp q) -> name cx TermMode locals qsp q) qs <> at loc)
  TCases e arms -> plain (term e <> foldMap (foldMap arm) arms)
  TInduction (Located vsp v) gen arms ->
    plain (occurrence vsp v <> foldMap (\g -> keywordBefore cx (location g) "generalizing") (take 1 gen) <> foldMap (\(Located gsp g) -> occurrence gsp g) gen <> foldMap (foldMap arm) arms)
  TObtain ns e -> let (ix, ls) = introduce ns in (ix <> term e, ls)
  TExists es -> plain (foldMap term es)
  THave mn ty rhs ->
    ( keyword <> maybe mempty (\(Located nsp _) -> token nsp SemanticTokenTypes_Variable [SemanticTokenModifiers_Declaration]) mn <> maybe mempty term ty <> rhsIndex cx locals (unLocated rhs)
    , maybe locals (\(Located _ n) -> Map.insert n SemanticTokenTypes_Variable locals) mn
    )
  TCalc c -> plain (calcIndex cx locals c)
  TRevert ns -> plain (foldMap (\(Located nsp n) -> occurrence nsp n) ns)
  TClear ns -> plain (foldMap (\(Located nsp n) -> occurrence nsp n) ns)
  TByCases (Located hsp h) e -> (keyword <> token hsp SemanticTokenTypes_Variable [SemanticTokenModifiers_Declaration] <> term e, Map.insert h SemanticTokenTypes_Variable locals)
  TTry u -> nested u
  TRepeat u -> nested u
  TAllGoals u -> nested u
  TAnyGoals u -> nested u
  TFirst us -> plain (foldMap (fst . tacticIndex cx locals) us)
  TThenAll u v ->
    let (iu, l1) = tacticIndex cx locals u
        (iv, l2) = tacticIndex cx l1 v
     in (iu <> iv, l2)
  TFocus ts -> (tacticsIndex cx locals ts, locals)
  TCase (Located csp c) ns ts -> plain (constructorOf csp c <> declareAll SemanticTokenTypes_Variable ns <> tacticsIndex cx (bindAll SemanticTokenTypes_Variable ns locals) ts)
  where
    keyword = keywordAt cx sp
    plain ix = (keyword <> ix, locals)
    term = expr cx TermMode locals
    introduce ns = (keyword <> declareAll SemanticTokenTypes_Variable ns, bindAll SemanticTokenTypes_Variable ns locals)
    nested u = plain (fst (tacticIndex cx locals u))
    rule (RewriteRule _ e) = term e
    at = \case
      AtGoal -> mempty
      AtHypotheses hs -> foldMap (\h -> keywordBefore cx (location h) "at") (take 1 hs) <> foldMap (\(Located hsp h) -> occurrence hsp h) hs
    occurrence osp x = token osp (Map.findWithDefault SemanticTokenTypes_Variable x locals) []
    arm (Located _ (Arm (Located csp c) ns body)) = constructorOf csp c <> declareAll SemanticTokenTypes_Variable ns <> tacticsIndex cx (bindAll SemanticTokenTypes_Variable ns locals) body
    constructorOf csp c = fromMaybe mempty (bareConstructor cx csp c)
    secondWord w = case wordAfter (cxLines cx) (spanStart sp) of
      Just (wsp, w') | w' == w -> token wsp SemanticTokenTypes_Keyword []
      _ -> mempty

-- | The word a tactic starts with, when it is one of the tactic language.
keywordAt :: Cx -> Span -> Index
keywordAt cx (Span start _) = case wordAt (cxLines cx) start of
  Just (wsp, w) | Set.member w tacticWords -> token wsp SemanticTokenTypes_Keyword []
  _ -> mempty

-- | The word before a position, when it is the one expected: @at@ before the hypotheses of a rewrite, @generalizing@ before the names of an induction.
keywordBefore :: Cx -> Span -> Text -> Index
keywordBefore cx (Span start _) w = case wordBefore (cxLines cx) start of
  Just (wsp, w') | w' == w -> token wsp SemanticTokenTypes_Keyword []
  _ -> mempty

-- | The words of an import, an opening or a renaming which are words only there: @as@ and @to@.
importWords :: Cx -> Located Decl -> Index
importWords cx (Located sp d) = case d of
  DImport _ -> keywords ["as", "to"]
  DOpenImport _ _ -> keywords ["as", "to"]
  DOpen _ dirs _ | not (null (dirRenaming dirs)) -> keywords ["to"]
  _ -> mempty
  where
    keywords ws = mconcat [token wsp SemanticTokenTypes_Keyword [] | (wsp, w) <- wordsIn (cxLines cx) sp, w `elem` ws]

-- * Words of the source

isWordChar :: Char -> Bool
isWordChar c = isAlphaNum c || c == '_' || c == '\''

-- | The word starting at a position, line and column from 1, when one does.
wordAt :: Lines -> (Int, Int) -> Maybe (Span, Text)
wordAt ls (l, c) =
  let line = lineAt ls l
      i = columnToChar line c
      w = T.takeWhile isWordChar (T.drop i line)
   in if T.null w || not (isWordStart (T.head w)) then Nothing else Just (Span (l, c) (l, c + T.length w), w)
  where
    isWordStart ch = not (ch `elem` ['0' .. '9'])

-- | The word after the one at a position, on the same line, separated by spaces only.
wordAfter :: Lines -> (Int, Int) -> Maybe (Span, Text)
wordAfter ls (l, c) = do
  (Span _ (_, c'), _) <- wordAt ls (l, c)
  let line = lineAt ls l
      i = columnToChar line c'
      spaces = T.length (T.takeWhile (== ' ') (T.drop i line))
  if spaces == 0 then Nothing else wordAt ls (l, charToColumn line (i + spaces))

-- | The word ending before a position, on the same line, separated by spaces only.
wordBefore :: Lines -> (Int, Int) -> Maybe (Span, Text)
wordBefore ls (l, c) =
  let line = lineAt ls l
      i = columnToChar line c
      before = T.take i line
      trimmed = T.dropWhileEnd (== ' ') before
      w = T.takeWhileEnd isWordChar trimmed
      j = T.length trimmed
   in if T.null w || T.length trimmed == T.length before then Nothing else Just (Span (l, charToColumn line (j - T.length w)) (l, charToColumn line j), w)

-- | Every word within a span, with where it is.
wordsIn :: Lines -> Span -> [(Span, Text)]
wordsIn ls (Span (l0, c0) (l1, c1)) = concatMap onLine [l0 .. l1]
  where
    onLine l =
      let line = lineAt ls l
          from = if l == l0 then columnToChar line c0 else 0
          to = if l == l1 then columnToChar line c1 else T.length line
       in [(Span (l, charToColumn line a) (l, charToColumn line b), w) | (a, b, w) <- wordRuns (T.take (to - from) (T.drop from line)) from]
    wordRuns text offset = go offset (T.unpack text)
      where
        go i cs = case cs of
          [] -> []
          ch : _
            | isWordChar ch && not (isSpace ch) ->
                let (w, rest) = span isWordChar cs
                    n = length w
                 in (i, i + n, T.pack w) : go (i + n) rest
            | otherwise -> go (i + 1) (drop 1 cs)
