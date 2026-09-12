{-# LANGUAGE OverloadedStrings #-}

{- | Variadic schemas and the binder sugar of the equation language, as a
source-to-source pass preceding name resolution.

A schema whose head has a variadic argument group @$[xs]@ is a template: its
instance at @k@ variadic arguments is an ordinary schema, obtained by
expanding the group into @k@ fresh pattern variables and every @$[xs]@ of its
clauses into those variables. Instances are generated on demand, at each
application whose argument count determines @k@, and are named after the
template and @k@. A template is also checked at zero and at one variadic
argument: every arity constraint it induces is affine in @k@, so those two
instances validate all of them, and the remaining checks do not depend on
@k@ at all.

A bounded search @μ i < b. body@ is sugar for the @mu@ schema in scope, and a
bounded quantifier over a code for the schema it searches with: @∀ i < b.
body@ is @holdsBelow@, and @∃ i < b. body@ is @mu@ compared with @b@.  The
schema is applied to a lambda closed over the maximal subterms of the body
which do not mention @i@, numerals included, then to the bound and those
subterms: @mu {λ i y₁ … yₖ. body'} b s₁ … sₖ@.  This makes the lambda
canonical, the same whatever the captured terms become; a body which is a
function applied to @i@ alone is that function.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic (
  ExpandedFamily (..),
  expandedEquations,
  expandFamily,
  expandTerm,
  instanceName,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, gets, modify', runStateT)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import GHC.TypeNats (natVal)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Numeric.Natural (Natural)

-- | The family with templates removed and the instances they demanded added.
data ExpandedFamily = ExpandedFamily
  { expandedEnv :: !Env
  -- ^ the initial environment, plus local templates and imported instances
  , expandedConcrete :: ![Equation T.Text]
  -- ^ the clauses without a variadic group, in their original order
  , expandedInstanceClauses :: ![((T.Text, Natural), [Equation T.Text])]
  -- ^ each generated instance's clauses, in the order of the template's
  , expandedTemplates :: !(Map T.Text VariadicTemplate)
  , expandedInstances :: !(Set T.Text)
  -- ^ every instance schema generated, whether demanded or only checked
  }

-- | The concrete clauses followed by those of every generated instance.
expandedEquations :: ExpandedFamily -> [Equation T.Text]
expandedEquations expanded = expandedConcrete expanded <> concatMap snd (expandedInstanceClauses expanded)

-- | The name of a template's instance at a number of variadic arguments.
instanceName :: T.Text -> Natural -> T.Text
instanceName ident k = ident <> "@" <> T.pack (show k)

data Ctx = Ctx
  { ctxPatternVars :: ![T.Text]
  , ctxBinders :: ![[IrrelevantName]]
  -- ^ enclosing binder groups, innermost first
  , ctxSplat :: !(Maybe (T.Text, [T.Text]))
  -- ^ the variadic group of the enclosing template and its expansion
  }

data St = St
  { stEnv :: !Env
  , stTemplates :: !(Map T.Text VariadicTemplate)
  , stDone :: !(Map (T.Text, Natural) [Equation T.Text])
  , stActive :: !(Map T.Text Natural)
  , stInstances :: !(Set T.Text)
  }

type M = StateT St (Either ElaborationError)

throw :: ElaborationError -> M a
throw = lift . Left

{- | Expand a family. The demands are instances required besides those the
equations apply; when checking, every local template is also instantiated at
zero and at one variadic argument.
-}
expandFamily :: Bool -> Env -> [(T.Text, Natural)] -> [Equation T.Text] -> Either ElaborationError ExpandedFamily
expandFamily checkTemplates env demands equations = do
  templates <- collectTemplates env equations
  let concrete = filter (\eq -> Map.notMember (name eq) templates) equations
      initial =
        St
          { stEnv = Map.union env (Map.map VariadicDef templates)
          , stTemplates = templates
          , stDone = Map.empty
          , stActive = Map.empty
          , stInstances = Set.empty
          }
  (rewritten, final) <- flip runStateT initial do
    eqs <- traverse (rewriteEquation Nothing) concrete
    forM_ demands (uncurry instantiate)
    when checkTemplates $ forM_ (Map.keys templates) \ident -> do
      instantiate ident 0
      instantiate ident 1
    pure eqs
  pure
    ExpandedFamily
      { expandedEnv = stEnv final
      , expandedConcrete = rewritten
      , expandedInstanceClauses = filter (not . null . snd) (Map.toList (stDone final))
      , expandedTemplates = templates
      , expandedInstances = stInstances final
      }

{- | Desugar the binder sugar of one term and redirect its applications of
variadic schemas to their instances, as for a clause whose pattern variables
are the given names. The instances of imported variadic schemas are added to
the environment returned.
-}
expandTerm :: Env -> [T.Text] -> EqTerm T.Text -> Either ElaborationError (Env, EqTerm T.Text)
expandTerm env vars term = do
  (rewritten, final) <-
    runStateT
      (rewrite (Ctx vars [] Nothing) term)
      St
        { stEnv = env
        , stTemplates = Map.empty
        , stDone = Map.empty
        , stActive = Map.empty
        , stInstances = Set.empty
        }
  pure (stEnv final, rewritten)

-- | Templates are the definitions with a variadic group in every clause.
collectTemplates :: Env -> [Equation T.Text] -> Either ElaborationError (Map T.Text VariadicTemplate)
collectTemplates env equations = foldM add Map.empty (nub (map name (filter (isJust . variadic) equations)))
  where
    add acc ident = do
      let clauses = filter ((== ident) . name) equations
      when (Map.member ident env) (Left (FunctionAlreadyDefined ident))
      splats <- maybe (Left (MissingVariadicGroup ident)) Right (traverse variadic clauses)
      splat <- case splats of
        s : rest
          | all (\r -> splatPosition r == splatPosition s && splatName r == splatName s) rest -> Right s
          | otherwise -> Left (InconsistentVariadicGroup ident)
        [] -> Left (InternalError ("collectTemplates: no clauses for " <> T.unpack ident))
      param <- case nub (map schemaParams clauses) of
        [[p]] -> Right p
        [[]] -> Left (VariadicWithoutParameter ident)
        [_] -> Left (TooManyVariadicParameters ident)
        _ -> Left (InconsistentSchemaDefinition ident)
      fixed <- case nub (map (length . args) clauses) of
        [n] -> Right (fromIntegral n)
        _ -> Left (InconsistentArity ident)
      pArity <- case paramShape param clauses of
        Just (a, 1) -> Right a
        Just (_, times) -> Left (VariadicParameterGroupMismatch ident param (splatName splat) times)
        Nothing -> Left (VariadicParameterUnapplied ident param (splatName splat))
      pure
        ( Map.insert
            ident
            VariadicTemplate
              { templateName = ident
              , templateParam = param
              , templateFixedArity = fixed
              , templateParamArity = pArity
              , templateEquations = clauses
              }
            acc
        )

-- | The fixed arguments and variadic groups in the first application of a parameter.
paramShape :: T.Text -> [Equation T.Text] -> Maybe (Natural, Natural)
paramShape param = foldr ((<|>) . find . clause) Nothing
  where
    find term = case term of
      LitET _ -> Nothing
      NameET _ -> Nothing
      BoundET _ _ -> Nothing
      SplatET _ -> Nothing
      InfixET l _ r -> find l <|> find r
      IfThenElseET c t e -> find c <|> find t <|> find e
      LamET _ body -> find body
      MuET _ bound body -> find bound <|> find body
      QuantET _ _ bound body -> find bound <|> find body
      _ :@ _ -> case spine term of
        (NameET h, arguments)
          | h == param ->
              let splats = length (filter isSplat arguments)
               in Just (fromIntegral (length arguments - splats), fromIntegral splats)
        (h, arguments) -> find h <|> foldr ((<|>) . find) Nothing arguments
    isSplat SplatET {} = True
    isSplat _ = False

spine :: EqTerm name -> (EqTerm name, [EqTerm name])
spine = go []
  where
    go xs (f :@ x) = go (x : xs) f
    go xs f = (f, xs)

patternVariables :: [Pattern T.Text] -> [T.Text]
patternVariables = concatMap go
  where
    go (VarP v) = [v]
    go (SuccP p) = go p
    go ZeroP = []

-- | Rewrite one clause; a template clause is expanded at the given instance.
rewriteEquation :: Maybe (VariadicTemplate, Natural) -> Equation T.Text -> M (Equation T.Text)
rewriteEquation Nothing eq = do
  body <- rewrite (Ctx (patternVariables (args eq)) [] Nothing) (clause eq)
  pure eq {clause = body}
rewriteEquation (Just (tmpl, k)) eq = do
  splat <- maybe (throw (InternalError "rewriteEquation: a template clause without a variadic argument")) pure (variadic eq)
  let vars = [splatName splat <> "$" <> T.pack (show i) | i <- take (fromIntegral k) [0 :: Int ..]]
      expanded = case splatPosition splat of
        SplatFirst -> map VarP vars <> args eq
        SplatLast -> args eq <> map VarP vars
  body <- rewrite (Ctx (patternVariables expanded) [] (Just (splatName splat, vars))) (clause eq)
  pure
    Equation
      { name = instanceName (templateName tmpl) k
      , schemaParams = [templateParam tmpl]
      , args = expanded
      , variadic = Nothing
      , clause = body
      }

rewrite :: Ctx -> EqTerm T.Text -> M (EqTerm T.Text)
rewrite ctx term = case term of
  LitET _ -> pure term
  BoundET _ _ -> pure term
  NameET _ -> rewriteApp ctx term
  _ :@ _ -> rewriteApp ctx term
  InfixET l op r -> InfixET <$> rewrite ctx l <*> pure op <*> rewrite ctx r
  IfThenElseET c t e -> IfThenElseET <$> rewrite ctx c <*> rewrite ctx t <*> rewrite ctx e
  LamET hints body -> LamET hints <$> rewrite ctx {ctxBinders = hints : ctxBinders ctx} body
  MuET hint bound body -> desugarMu ctx hint bound body
  QuantET q hint bound body -> desugarQuant ctx q hint bound body
  SplatET xs -> throw (SplatOutsideArgument xs)

rewriteApp :: Ctx -> EqTerm T.Text -> M (EqTerm T.Text)
rewriteApp ctx term = do
  let (hd, rawArgs) = spine term
  arguments <- concat <$> traverse expand rawArgs
  hd' <- case hd of
    NameET _ -> rewriteHead ctx hd (length arguments)
    _ -> rewrite ctx hd
  pure (foldl (:@) hd' arguments)
  where
    expand (SplatET xs) = case ctxSplat ctx of
      Just (group, vars) | group == xs -> pure (map NameET vars)
      Just (group, _) -> throw (UnknownVariadicGroup xs group)
      Nothing -> throw (SplatOutsideVariadicSchema xs)
    expand t = (: []) <$> rewrite ctx t

-- | An application of a variadic schema is redirected to its instance.
rewriteHead :: Ctx -> EqTerm T.Text -> Int -> M (EqTerm T.Text)
rewriteHead ctx hd count = case hd of
  NameET ident
    | ident `elem` ctxPatternVars ctx -> pure hd
    | otherwise -> do
        env <- gets stEnv
        case Map.lookup ident env of
          Just (VariadicDef tmpl) -> instanceHead ident (templateFixedArity tmpl)
          Just (ImportedVariadic _ fixed _ _) -> instanceHead ident fixed
          _ -> pure hd
  _ -> pure hd
  where
    instanceHead ident fixed = do
      when (fromIntegral count < 1 + fixed) $
        throw (TooFewVariadicArguments ident fixed count)
      let k = fromIntegral count - 1 - fixed
      instantiate ident k
      pure (NameET (instanceName ident k))

instantiate :: T.Text -> Natural -> M ()
instantiate ident k = do
  done <- gets (Map.member (ident, k) . stDone)
  active <- gets (Map.lookup ident . stActive)
  case active of
    Just k'
      | k' == k -> pure ()
      | otherwise -> throw (VariadicRecursionChangesArity ident k' k)
    Nothing -> unless done do
      entry <- gets (Map.lookup ident . stEnv)
      case entry of
        Just (VariadicDef tmpl) -> do
          modify' (\s -> s {stActive = Map.insert ident k (stActive s)})
          clauses <- traverse (rewriteEquation (Just (tmpl, k))) (templateEquations tmpl)
          modify' \s ->
            s
              { stActive = Map.delete ident (stActive s)
              , stDone = Map.insert (ident, k) clauses (stDone s)
              , stInstances = Set.insert (instanceName ident k) (stInstances s)
              }
        Just (ImportedVariadic _ fixed pArity instantiation) -> do
          inst <- either (throw . SchemaFailure) pure (instantiation k)
          let instName = instanceName ident k
          modify' \s ->
            s
              { stEnv = Map.insert instName (ImportedSchema instName (pArity + k) (fixed + k) inst) (stEnv s)
              , stDone = Map.insert (ident, k) [] (stDone s)
              , stInstances = Set.insert instName (stInstances s)
              }
        _ -> throw (UnknownVariadicSchema ident)

-- | A bounded search @μ i < b. body@ is the search of the schema @mu@ in scope, see 'searchWith'.
desugarMu :: Ctx -> IrrelevantName -> EqTerm T.Text -> EqTerm T.Text -> M (EqTerm T.Text)
desugarMu ctx hint bound body = do
  env <- gets stEnv
  unless (Map.member "mu" env) $
    throw BoundedSearchOutOfScope
  fst <$> searchWith ctx "mu" hint bound body

{- | A bounded quantifier over a code is the search of the schema it searches
with: @∀ i < b. body@ that of @holdsBelow@, and @∃ i < b. body@ that of @mu@
compared with the bound.
-}
desugarQuant :: Ctx -> Quantifier -> IrrelevantName -> EqTerm T.Text -> EqTerm T.Text -> M (EqTerm T.Text)
desugarQuant ctx q hint bound body = do
  env <- gets stEnv
  let schema = quantifierSchema q
  unless (Map.member schema env) $
    throw (QuantifierOutOfScope schema)
  (search, bound') <- searchWith ctx schema hint bound body
  pure case q of
    Forall -> search
    Exists -> InfixET search "<" bound'

{- | The schema applied to the canonical closure of the body and to the bound,
with the bound: @schema {λ i y₁ … yₖ. body'} b s₁ … sₖ@, where the @sⱼ@ are the
maximal subterms of the body which do not mention @i@, in the order they occur,
numerals included, and @body'@ is the body with each replaced by its @yⱼ@.
Unlike capturing variables, this makes the lambda canonical, the same function
whatever the captured terms become, as "Language.Praxis.PRA.Syntax" abstracts
a term.  A body which is a function applied to @i@ alone is that function, the
parameter itself.  Inner binders are desugared first, so only closed lambdas
remain beneath the body.
-}
searchWith :: Ctx -> T.Text -> IrrelevantName -> EqTerm T.Text -> EqTerm T.Text -> M (EqTerm T.Text, EqTerm T.Text)
searchWith ctx schema hint bound body = do
  bound' <- rewrite ctx bound
  body' <- rewrite ctx {ctxBinders = [hint] : ctxBinders ctx} body
  env <- gets stEnv
  instances <- gets stInstances
  let (slots, closed) = captureSlots ctx env instances body'
      param = case closed of
        NameET f :@ BoundET 0 0 | null slots, unary env f -> NameET f
        _ -> LamET (hint : map (const (IrrelevantName "y")) slots) closed
  hd <- rewriteHead ctx (NameET schema) (2 + length slots)
  pure (foldl (:@) hd (param : bound' : slots), bound')
  where
    -- A function of one argument: of the environment, or a name it lacks
    -- which is no variable, as an abstract function of a rule, a parameter
    -- of a schema or a definition of the same block, whose arity is checked
    -- where it is resolved.
    unary env f
      | f `elem` ctxPatternVars ctx = False
      | otherwise = case Map.lookup f env of
          Just (SomeFunction (_ :: Function m)) -> natVal (Proxy @m) == 1
          Just _ -> False
          Nothing -> True

{- | The maximal subterms of a body, under the binder of depth 0, which do not
mention it, in the order they occur, as they read outside the binder; and the
body with the @j@-th of them, from 0, replaced by @BoundET 0 (1 + j)@.  Such a
subterm is a numeral, a variable of the clause, an outer binder, a constant or
an application; a function standing as the parameter of a schema is none.
-}
captureSlots :: Ctx -> Env -> Set T.Text -> EqTerm T.Text -> ([EqTerm T.Text], EqTerm T.Text)
captureSlots ctx env instances = go []
  where
    go acc t
      | slot t, not (occurs 0 t) = (acc <> [shift 0 t], BoundET 0 (1 + length acc))
      | otherwise = case t of
          _ :@ _ -> case spine t of
            (h, arguments) ->
              let (parameters, rest) = splitAt (schemaParameters h) arguments
                  (acc', rest') = goMany acc rest
               in (acc', foldl (:@) h (parameters <> rest'))
          InfixET l op r ->
            let (a1, l') = go acc l
                (a2, r') = go a1 r
             in (a2, InfixET l' op r')
          IfThenElseET c x e ->
            let (a1, c') = go acc c
                (a2, x') = go a1 x
                (a3, e') = go a2 e
             in (a3, IfThenElseET c' x' e')
          _ -> (acc, t)
    goMany acc [] = (acc, [])
    goMany acc (x : xs) =
      let (a1, x') = go acc x
          (a2, xs') = goMany a1 xs
       in (a2, x' : xs')

    slot = \case
      LitET _ -> True
      BoundET d _ -> d > 0
      NameET "_" -> True
      NameET x
        | x `elem` ctxPatternVars ctx -> True
        | Just (SomeFunction (_ :: Function m)) <- Map.lookup x env -> natVal (Proxy @m) == 0
        | otherwise -> False
      _ :@ _ -> True
      InfixET {} -> True
      IfThenElseET {} -> True
      _ -> False

    -- The leading arguments of an application of a schema: its parameters, functions rather than terms.
    schemaParameters = \case
      NameET h
        | Set.member h instances -> 1
        | otherwise -> case Map.lookup h env of
            Just (SchemaDef _ params _ _) -> length params
            Just ImportedSchema {} -> 1
            Just ImportedVariadic {} -> 1
            Just VariadicDef {} -> 1
            _ -> 0
      _ -> 0

    occurs :: Int -> EqTerm T.Text -> Bool
    occurs level = \case
      BoundET d _ -> d == level
      f :@ x -> occurs level f || occurs level x
      InfixET l _ r -> occurs level l || occurs level r
      IfThenElseET c x e -> occurs level c || occurs level x || occurs level e
      LamET _ b -> occurs (level + 1) b
      MuET _ b x -> occurs level b || occurs (level + 1) x
      QuantET _ _ b x -> occurs level b || occurs (level + 1) x
      _ -> False

    -- Outside the binder, an occurrence of an enclosing binder is one group nearer.
    shift :: Int -> EqTerm T.Text -> EqTerm T.Text
    shift level = \case
      BoundET d p | d > level -> BoundET (d - 1) p
      f :@ x -> shift level f :@ shift level x
      InfixET l op r -> InfixET (shift level l) op (shift level r)
      IfThenElseET c x e -> IfThenElseET (shift level c) (shift level x) (shift level e)
      LamET hs b -> LamET hs (shift (level + 1) b)
      t -> t
