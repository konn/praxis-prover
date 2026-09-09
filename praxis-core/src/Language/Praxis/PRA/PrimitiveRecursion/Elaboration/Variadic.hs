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

A bounded search @μ i < b. body@ is sugar for the @mu@ schema in scope,
applied to a lambda closed over the variables the body captures:
@mu {λ i y₁ … yₖ. body} b y₁ … yₖ@, where the @yᵢ@ are the pattern variables
and enclosing binders occurring in the body, in order of first occurrence.
-}
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic (
  ExpandedFamily (..),
  expandedEquations,
  expandFamily,
  instanceName,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, gets, modify', runStateT)
import Data.List (elemIndex, nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
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

data Capture = CapturedPattern !T.Text | CapturedBinder !Int !Int
  deriving (Eq)

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

type M = StateT St (Either String)

throw :: String -> M a
throw = lift . Left

{- | Expand a family. The demands are instances required besides those the
equations apply; when checking, every local template is also instantiated at
zero and at one variadic argument.
-}
expandFamily :: Bool -> Env -> [(T.Text, Natural)] -> [Equation T.Text] -> Either String ExpandedFamily
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

-- | Templates are the definitions with a variadic group in every clause.
collectTemplates :: Env -> [Equation T.Text] -> Either String (Map T.Text VariadicTemplate)
collectTemplates env equations = foldM add Map.empty (nub (map name (filter (isJust . variadic) equations)))
  where
    add acc ident = do
      let clauses = filter ((== ident) . name) equations
          shown = T.unpack ident
      when (Map.member ident env) (Left ("Function already defined: " <> shown))
      splats <- maybe (Left ("Every clause of " <> shown <> " must declare its variadic argument $[..]")) Right (traverse variadic clauses)
      splat <- case splats of
        s : rest
          | all (\r -> splatPosition r == splatPosition s && splatName r == splatName s) rest -> Right s
          | otherwise -> Left ("Clauses of " <> shown <> " must agree on the name and position of their variadic argument")
        [] -> Left ("No clauses for " <> shown)
      param <- case nub (map schemaParams clauses) of
        [[p]] -> Right p
        [[]] -> Left ("Variadic arguments require a schema parameter: " <> shown)
        [_] -> Left ("A variadic schema takes exactly one schema parameter: " <> shown)
        _ -> Left ("Inconsistent schema definition for " <> shown)
      fixed <- case nub (map (length . args) clauses) of
        [n] -> Right (fromIntegral n)
        _ -> Left ("Inconsistent arity for " <> shown)
      pArity <- case paramShape param clauses of
        Just (a, 1) -> Right a
        Just _ -> Left ("The parameter " <> T.unpack param <> " of " <> shown <> " must take the variadic arguments $[" <> T.unpack (splatName splat) <> "] exactly once")
        Nothing -> Left ("The parameter " <> T.unpack param <> " of " <> shown <> " must be applied to the variadic arguments $[" <> T.unpack (splatName splat) <> "]")
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
  splat <- maybe (throw "Internal: template clause without a variadic argument") pure (variadic eq)
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
  SplatET xs -> throw ("The variadic arguments $[" <> T.unpack xs <> "] may only be passed as arguments")

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
      Just (group, _) -> throw ("Unknown variadic argument $[" <> T.unpack xs <> "]; the enclosing schema declares $[" <> T.unpack group <> "]")
      Nothing -> throw ("The variadic arguments $[" <> T.unpack xs <> "] are only available inside a variadic schema")
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
      let least = 1 + fixed
      when (fromIntegral count < least) $
        throw (T.unpack ident <> " takes at least " <> show least <> " arguments (its parameter and " <> show fixed <> " fixed ones), given " <> show count)
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
      | otherwise ->
          throw
            ( "Variadic schema "
                <> T.unpack ident
                <> " applies itself with "
                <> show k
                <> " variadic arguments while being instantiated with "
                <> show k'
                <> "; recursion must preserve the number of variadic arguments"
            )
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
          inst <- either throw pure (instantiation k)
          let instName = instanceName ident k
          modify' \s ->
            s
              { stEnv = Map.insert instName (ImportedSchema instName (pArity + k) (fixed + k) inst) (stEnv s)
              , stDone = Map.insert (ident, k) [] (stDone s)
              , stInstances = Set.insert instName (stInstances s)
              }
        _ -> throw ("Unknown variadic schema: " <> T.unpack ident)

{- | Inner searches are desugared first, so afterwards only closed lambdas
remain beneath the body and every capture is visible at its top level.
-}
desugarMu :: Ctx -> IrrelevantName -> EqTerm T.Text -> EqTerm T.Text -> M (EqTerm T.Text)
desugarMu ctx hint bound body = do
  bound' <- rewrite ctx bound
  body' <- rewrite ctx {ctxBinders = [hint] : ctxBinders ctx} body
  let captured = nub (captures 0 body')
      binders = hint : map captureHint captured
      closed = close captured 0 body'
      arguments = map captureArgument captured
  env <- gets stEnv
  unless (Map.member "mu" env) $
    throw "A bounded search 'μ i < b. body' requires a schema 'mu' to be in scope"
  hd <- rewriteHead ctx (NameET "mu") (2 + length captured)
  pure (foldl (:@) hd (LamET binders closed : bound' : arguments))
  where
    captures level = \case
      BoundET depth position
        | level == 0, depth >= 1 -> [CapturedBinder (depth - 1) position]
        | otherwise -> []
      NameET ident
        | level == 0, ident `elem` ctxPatternVars ctx -> [CapturedPattern ident]
        | otherwise -> []
      LitET _ -> []
      SplatET _ -> []
      f :@ x -> captures level f <> captures level x
      InfixET l _ r -> captures level l <> captures level r
      IfThenElseET c t e -> captures level c <> captures level t <> captures level e
      LamET _ inner -> captures (level + 1 :: Int) inner
      MuET _ b inner -> captures level b <> captures (level + 1) inner
    close captured level = \case
      t@(BoundET depth position)
        | level == 0, depth >= 1 -> BoundET 0 (position' (CapturedBinder (depth - 1) position))
        | otherwise -> t
      t@(NameET ident)
        | level == 0, Just index <- elemIndex (CapturedPattern ident) captured -> BoundET 0 (1 + index)
        | otherwise -> t
      t@(LitET _) -> t
      t@(SplatET _) -> t
      f :@ x -> close captured level f :@ close captured level x
      InfixET l op r -> InfixET (close captured level l) op (close captured level r)
      IfThenElseET c t e -> IfThenElseET (close captured level c) (close captured level t) (close captured level e)
      LamET hints inner -> LamET hints (close captured (level + 1 :: Int) inner)
      MuET h b inner -> MuET h (close captured level b) (close captured (level + 1) inner)
      where
        position' capture = maybe 0 (1 +) (elemIndex capture captured)
    captureHint (CapturedPattern ident) = IrrelevantName ident
    captureHint (CapturedBinder depth position) = case drop depth (ctxBinders ctx) of
      (group : _) | position < length group -> group !! position
      _ -> IrrelevantName "x"
    captureArgument (CapturedPattern ident) = NameET ident
    captureArgument (CapturedBinder depth position) = BoundET depth position
