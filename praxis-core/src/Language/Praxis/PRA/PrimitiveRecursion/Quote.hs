{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{- | Compile complete equation families at compile time into @Function n@
bindings referring to shared definitions. A headerless quote is independent
and exports @fSignature@ for each function @f@, all sharing the same snapshot.
A header such as
@environment arithmetic extends basic@ also emits @arithmetic :: Signature@
and registers an immutable snapshot for subsequent declaration quotes in the
same module. All clauses of a function must occur in one block.

A schema @s {P} …@ becomes a function of its parameter, and a variadic schema
@s {P} … $[xs]@ a function polymorphic in the parameter's arity, whose
instances are elaborated on demand from the lifted template.

To reuse an imported signature, define @prfQuoter importedSignature@ in a
support module and import that quasiquoter where it is used, as for
"Language.Praxis.PRA.Tactic.Quote". No module-local state crosses module
boundaries. Expression, pattern and type quotes are deliberately unsupported.
Parsing, coverage, recursion and dependency checking run during compilation;
the generated signature contains precompiled programs and checks its table
invariants when first demanded. Calls are never recursively expanded here.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Quote (
  prf,
  prfQuoter,
) where

import Control.Monad (unless, void, when)
import Data.Char (isAlphaNum, isLower)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import GHC.TypeNats (KnownNat, SomeNat (..), someNatVal, type (+), type (-), type (<=))
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift, getQ, lift, liftTyped, mkNameG_v, putQ, unTypeCode)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Parser
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (Equation (..), VariadicTemplate (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic
import Language.Praxis.PRA.PrimitiveRecursion.Environment
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.TH.Internal (arityType)
import Language.Praxis.PRA.Signature qualified as Sig
import Language.Praxis.TH.Internal qualified as QTH
import Numeric.Natural (Natural)
import Text.Megaparsec (SourcePos (..), eof, errorBundlePretty, getSourcePos, optional, parse, sourcePosPretty, try, (<|>))

data Header = Header !T.Text !(Maybe T.Text)

-- A private type keeps this registry separate from other TH clients' state.
data Registry = Registry
  { snapshots :: !(Map T.Text (CompiledEnv, Sig.Signature))
  , generatedNames :: !(Set T.Text)
  }

-- | A declaration quasiquoter with only S and Succ initially in scope.
prf :: QuasiQuoter
prf = prfQuoter mempty

{- | Initial codes must be finite. Named signature entries are emitted as
Haskell references; unnamed entries are lifted structurally.
-}
prfQuoter :: Sig.Signature -> QuasiQuoter
prfQuoter initial =
  QuasiQuoter
    { quoteDec = compileQuote initial
    , quoteExp = unsupported "expression"
    , quotePat = unsupported "pattern"
    , quoteType = unsupported "type"
    }
  where
    unsupported context _ = fail ("prf: " <> context <> " quotes are unsupported; use a declaration quote")

quoteP :: Parser (Maybe Header, [LocatedEquation])
quoteP = (,) <$> optional (try headerP) <*> equationsP
  where
    headerP = do
      start <- getSourcePos
      reserved "environment"
      sameLine start
      ident <- anySymbol
      parent <- optional $ try $ do
        sameLine start
        reserved "extends"
        sameLine start
        anySymbol
      void (symbol ";") <|> do
        here <- getSourcePos
        unless (sourceLine here > sourceLine start) eof
      pure (Header ident parent)
    sameLine start = do
      here <- getSourcePos
      unless (sourceLine here == sourceLine start) (fail "environment header must be on one line")

compileQuote :: Sig.Signature -> String -> TH.Q [TH.Dec]
compileQuote initial source = do
  loc <- TH.location
  let (line, column) = TH.loc_start loc
      padded = T.replicate (line - 1) "\n" <> T.replicate (column - 1) " " <> T.pack source
  (header, equations) <- either (fail . errorBundlePretty) pure $ parse (spaceConsumer *> quoteP <* eof) (TH.loc_filename loc) padded
  registry <- maybe (Registry Map.empty Set.empty) id <$> getQ
  (parent, parentSig) <- case header of
    Just (Header _ (Just ident)) ->
      maybe (fail ("prf: unknown environment " <> T.unpack ident <> "; parents must be declared earlier in this module")) pure (Map.lookup ident (snapshots registry))
    _ -> pure (compiledEnvironment initial, initial)
  let raw = map locatedEquation equations
      functionNames = Set.fromList (map name raw)
      signatureNames = case header of
        Nothing -> Set.map (<> "Signature") functionNames
        Just (Header ident _) -> Set.singleton ident
      names = functionNames <> signatureNames
      at eq err = fail (sourcePosPretty (equationPosition eq) <> ": " <> err)
  unless (Set.null (functionNames `Set.intersection` signatureNames)) (fail "prf: generated signature and function names must differ")
  mapM_ (\eq -> unless (validBinding (name (locatedEquation eq))) (at eq "prf: function name must be a Haskell variable identifier")) equations
  case header of
    Nothing -> pure ()
    Just (Header ident _) -> do
      unless (validBinding ident) (fail "prf: environment name must be a Haskell variable identifier")
      when (Set.member ident functionNames) (fail "prf: environment and function names must differ")
      when (Map.member ident (snapshots registry)) (fail ("prf: environment already defined: " <> T.unpack ident))
  unless (Set.null (names `Set.intersection` generatedNames registry)) $
    fail ("prf: Haskell binding already generated: " <> show (Set.toList (names `Set.intersection` generatedNames registry)))
  -- Locate name/arity errors at the individual clause before compilation. An
  -- instance clause is attributed to the template clause it expands.
  expanded <- either fail pure (expandFamily True (signatureEnv parentSig) [] raw)
  renamingEnv <- either fail pure (equationEnv (expandedEnv expanded) (expandedEquations expanded))
  let concreteLocated = [eq | eq <- equations, isNothing (variadic (locatedEquation eq))]
      templateLocated ident = [eq | eq <- equations, name (locatedEquation eq) == ident]
      attributed =
        zip concreteLocated (expandedConcrete expanded)
          <> concat [zip (templateLocated ident) clauses | ((ident, _), clauses) <- expandedInstanceClauses expanded]
  mapM_ (\(located, eq) -> either (at located) (const (pure ())) (renameEquation renamingEnv eq)) attributed
  let qualify ident = T.pack (TH.loc_package loc <> ":" <> TH.loc_module loc <> ".") <> ident
  block <- either (fail . withLocations equations) pure (compileDefinitionsWith qualify parent raw)
  extended <- either fail pure (extendEnvironment parent block)
  let hsName ident = mkNameG_v (TH.loc_package loc) (TH.loc_module loc) (T.unpack ident)
      newSymbols =
        Sig.signatureWithVariadicSchemas
          [ sym {Sig.symbolHaskellName = Just (hsName (T.pack (Sig.symbolName sym)))}
          | sym <- Sig.symbols (blockSignature block)
          ]
          [ sch {Sig.schemaSymbolHaskellName = Just (hsName (T.pack (Sig.schemaSymbolName sch)))}
          | sch <- Sig.schemas (blockSignature block)
          ]
          [ sch {Sig.variadicSchemaHaskellName = Just (hsName (T.pack (Sig.variadicSchemaName sch)))}
          | sch <- Sig.variadicSchemas (blockSignature block)
          ]
  kernel <- either fail pure (Sig.signatureKernelEnv (environmentSignature extended))
  let fullSig = Sig.withKernelEnv kernel (newSymbols <> parentSig)
  signatureName <- case header of
    Just (Header ident _) -> pure (TH.mkName (T.unpack ident))
    Nothing -> TH.newName "prfSignature"
  declarations <- concat <$> traverse (emitDefinition qualify) (Map.elems (blockDefinitions block))
  schemaDeclarations <- concat <$> traverse (emitSchema qualify) (Map.elems (blockSchemas block))
  variadicDeclarations <- concat <$> traverse (emitVariadic signatureName) (Map.elems (blockVariadics block))
  signatureDeclarations <- case header of
    Nothing | null equations -> pure []
    Nothing -> do
      binding <- valueDeclaration signatureName [t|Sig.Signature|] (unTypeCode (liftSignature fullSig))
      aliases <- concat <$> traverse (\ident -> valueDeclaration (TH.mkName (T.unpack ident)) [t|Sig.Signature|] (QTH.varE signatureName)) (Set.toList signatureNames)
      pure (binding <> aliases)
    Just _ ->
      valueDeclaration signatureName [t|Sig.Signature|] (unTypeCode (liftSignature fullSig))
  let registered = case header of
        Nothing -> snapshots registry
        Just (Header ident _) -> Map.insert ident (extended, fullSig) (snapshots registry)
  putQ (Registry registered (names <> generatedNames registry))
  pure (declarations <> schemaDeclarations <> variadicDeclarations <> signatureDeclarations)

withLocations :: [LocatedEquation] -> String -> String
withLocations equations err = "prf: " <> err <> concatMap location equations
  where
    location eq = "\n  " <> T.unpack (name (locatedEquation eq)) <> " at " <> sourcePosPretty (equationPosition eq)

validBinding :: T.Text -> Bool
validBinding ident = case T.uncons ident of
  Just (c, rest) ->
    (isLower c || c == '_')
      && T.all (\x -> isAlphaNum x || x == '_' || x == '\'') rest
      && ident `notElem` ["_", "case", "class", "data", "default", "deriving", "do", "else", "foreign", "if", "import", "in", "infix", "infixl", "infixr", "instance", "let", "module", "newtype", "of", "then", "type", "where", "forall", "mdo", "family", "role", "pattern", "qualified", "as", "hiding"]
  Nothing -> False

emitDefinition :: (T.Text -> T.Text) -> ElaboratedDefinition -> TH.Q [TH.Dec]
emitDefinition qualify (ElaboratedDefinition ident (_ :: F.Program n) _ _ _) =
  valueDeclaration
    (TH.mkName (T.unpack ident))
    [t|F.Function $(arityType @n)|]
    (unTypeCode (liftTyped (F.Defined (F.DefId (qualify ident)) :: F.Function n)))

emitSchema :: (T.Text -> T.Text) -> ElaboratedSchema -> TH.Q [TH.Dec]
emitSchema _ (ElaboratedSchema ident params pArity (ElaboratedDefinition _ (code :: F.Program n) _ _ _)) =
  case someNatVal pArity of
    SomeNat (_ :: Proxy k) -> do
      let name = TH.mkName (T.unpack ident)
          paramName = TH.mkName "p"
          targetParam = case params of (p : _) -> p; [] -> "P"
          ty = [t|F.Function $(arityType @k) -> F.Function $(arityType @n)|]
          body = [|F.Inline (substProgram (F.DefId targetParam) (F.functionProgram $(TH.varE paramName)) $(unTypeCode (liftAtArity [t|F.Program|] code)))|]
      sigDec <- QTH.signature name ty
      funDec <- QTH.function name [([D.DVarP paramName], body)]
      pure [sigDec, funDec]

{- | A variadic schema is a function of its parameter, polymorphic in that
parameter's arity @m@; an instance has arity @m@ shifted by the constant
difference between the schema's fixed arguments and the parameter's. The
template is lifted so that instances can be elaborated at run time, in the
emitted signature.
-}
emitVariadic :: TH.Name -> VariadicTemplate -> TH.Q [TH.Dec]
emitVariadic signatureName tmpl = do
  m <- TH.newName "m"
  let binding = TH.mkName (T.unpack (templateName tmpl))
      fixed = templateFixedArity tmpl
      pArity = templateParamArity tmpl
      symbolE = [|templateSymbol $(lift tmpl) $(QTH.varE signatureName)|]
      mT = QTH.varT m
  (constraints, ty, body) <- case compare fixed pArity of
    EQ ->
      pure
        ( [[t|KnownNat $mT|]]
        , [t|F.Function $mT -> F.Function $mT|]
        , [|Sig.applyVariadicSame $symbolE|]
        )
    GT -> do
      let d = naturalType (fixed - pArity)
      pure
        ( [[t|KnownNat $mT|]]
        , [t|F.Function $mT -> F.Function ($mT + $d)|]
        , [|Sig.applyVariadicPlus @($d) $symbolE|]
        )
    LT -> do
      let d = naturalType (pArity - fixed)
      pure
        ( [[t|KnownNat $mT|], [t|$d <= $mT|]]
        , [t|F.Function $mT -> F.Function ($mT - $d)|]
        , [|Sig.applyVariadicMinus @($d) $symbolE|]
        )
  valueDeclaration binding (QTH.forallType [m] constraints ty) body

naturalType :: Natural -> TH.TypeQ
naturalType n = case someNatVal n of
  SomeNat (_ :: Proxy d) -> arityType @d

-- Declaration quotes permit a generated binding pattern, but not a generated
-- name on the left of a type signature. Keep that boundary in th-desugar.
valueDeclaration :: TH.Name -> TH.TypeQ -> TH.ExpQ -> TH.Q [TH.Dec]
valueDeclaration binding ty body = do
  signatureDeclaration <- QTH.signature binding ty
  declaration <- [d|$(QTH.varP binding) = $body|]
  pure (signatureDeclaration : declaration)

-- Preserve the concrete arity when lifting a value out of an existential
-- definition or symbol. The constructor traversal itself comes from DeriveLift.
liftAtArity :: forall n f. (KnownNat n, Lift (f n)) => TH.TypeQ -> f n -> TH.Code TH.Q (f n)
liftAtArity constructor value =
  -- Only the concrete type index crosses this untyped boundary. The value's
  -- recursive construction is checked by its derived Lift instance.
  TH.unsafeCodeCoerce [|$(unTypeCode (liftTyped value)) :: $constructor $(arityType @n)|]

liftSignature :: Sig.Signature -> TH.Code TH.Q Sig.Signature
liftSignature sig = TH.joinCode do
  env <- either fail pure (Sig.signatureKernelEnv sig)
  pure
    [||
    Sig.withKernelEnv
      (either error id (F.extendKernelEnv F.emptyKernelEnv $$(listCode (map definition (F.definitions env)))))
      ( Sig.signatureWithVariadicSchemas
          $$(listCode (map entry (Sig.symbols sig)))
          $$(listCode (map schemaEntry (Sig.schemas sig)))
          $$(listCode (map variadicEntry (Sig.variadicSchemas sig)))
      )
    ||]
  where
    definition (F.Definition ident code) = [||F.Definition $$(liftTyped ident) $$(liftAtArity [t|F.Program|] code)||]
    entry sym = case Sig.symbolFunction sym of
      F.SomeFunction (fun :: F.Function n) -> case (fun, Sig.symbolHaskellName sym) of
        (F.Primitive _, Just binding) -> [||Sig.symbolNamed $$(liftTyped (Sig.symbolName sym)) $$(liftTyped binding) $$(reference binding (F.Primitive @n))||]
        (_, Just binding) -> [||Sig.functionSymbolNamed $$(liftTyped (Sig.symbolName sym)) $$(liftTyped binding) $$(reference binding (id @(F.Function n)))||]
        (_, Nothing) -> [||Sig.functionSymbol $$(liftTyped (Sig.symbolName sym)) $$(liftAtArity [t|F.Function|] fun)||]
    schemaEntry (Sig.SchemaSymbol name (inst :: F.Function k -> F.Function n) hs) = case hs of
      Just binding -> [||Sig.schemaSymbolNamed $$(liftTyped name) $$(liftTyped binding) $$(referenceSchema binding (id @(F.Function k -> F.Function n)))||]
      Nothing -> [||Sig.schemaSymbol @k @n $$(liftTyped name) $$(referenceSchema (TH.mkName name) (id @(F.Function k -> F.Function n)))||]
    -- The instances of a variadic schema are recovered from its polymorphic
    -- binding, whose type the splice site checks; the shape of that type is
    -- determined by the recorded arities alone.
    variadicEntry sym = TH.unsafeCodeCoerce do
      let name = Sig.variadicSchemaName sym
          fixed = Sig.variadicSchemaFixedArity sym
          pArity = Sig.variadicSchemaParamArity sym
          binding = fromMaybe (TH.mkName name) (Sig.variadicSchemaHaskellName sym)
          instances = case compare fixed pArity of
            EQ -> [|Sig.variadicInstanceSame $(lift name) $(lift pArity) $(QTH.varE binding)|]
            GT -> [|Sig.variadicInstancePlus @($(naturalType (fixed - pArity))) $(lift name) $(lift pArity) $(QTH.varE binding)|]
            LT -> [|Sig.variadicInstanceMinus @($(naturalType (pArity - fixed))) $(lift name) $(lift pArity) $(QTH.varE binding)|]
      case Sig.variadicSchemaHaskellName sym of
        Just hs -> [|Sig.variadicSchemaSymbolNamed $(lift name) $(lift hs) $(lift fixed) $(lift pArity) $instances|]
        Nothing -> [|Sig.variadicSchemaSymbol $(lift name) $(lift fixed) $(lift pArity) $instances|]
    -- The signature records each referenced binding's type. The witness fixes
    -- its arity here; the splice site checks the actual Haskell binding again.
    reference :: TH.Name -> (a -> F.Function n) -> TH.Code TH.Q a
    reference binding _ = TH.unsafeCodeCoerce (QTH.varE binding)
    referenceSchema :: TH.Name -> (a -> (F.Function k -> F.Function n)) -> TH.Code TH.Q a
    referenceSchema binding _ = TH.unsafeCodeCoerce (QTH.varE binding)

listCode :: [TH.Code TH.Q a] -> TH.Code TH.Q [a]
listCode = foldr (\x xs -> [||$$x : $$xs||]) [||[]||]
