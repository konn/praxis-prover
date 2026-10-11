{-# LANGUAGE TemplateHaskell #-}

{- | Quotation boundaries for syntax whose size or names are known only at
splice time. All construction uses quotations or th-desugar, never TH's
version-dependent smart constructors.
-}
module Language.Praxis.TH.Internal (
  varE,
  conE,
  varT,
  conT,
  varP,
  listE,
  tupleE,
  listPattern,
  signature,
  function,
  lambdaCase,
  letBindings,
  forallType,
  strictField,
  bindStatement,
  statement,
  doBlock,
) where

import Data.Data (Data, cast, gmapQ, gmapT)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (catMaybes, fromMaybe)
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Syntax (Dec, Exp, Name, Pat, Q, Stmt, Type, newName)

varE, conE :: Name -> Q Exp
varE = pure . D.expToTH . D.DVarE
conE = pure . D.expToTH . D.DConE

varT, conT :: Name -> Q Type
varT = pure . D.typeToTH . D.DVarT
conT = pure . D.typeToTH . D.DConT

varP :: Name -> Q Pat
varP = pure . D.patToTH . D.DVarP

listE :: [Q Exp] -> Q Exp
listE = foldr (\x xs -> [|$x : $xs|]) [|[]|]

tupleE :: [Q Exp] -> Q Exp
tupleE = withExpressions (D.expToTH . D.mkTupleDExp)

listPattern :: [D.DPat] -> D.DPat
listPattern = foldr (\x xs -> D.DConP '(:) [] [x, xs]) (D.DConP '[] [] [])

signature :: Name -> Q Type -> Q Dec
signature name ty = D.letDecToTH . D.DSigD name <$> (ty >>= D.dsType)

function :: Name -> [([D.DPat], Q Exp)] -> Q Dec
function name clauses =
  withExpressions
    (D.letDecToTH . D.DFunD name . zipWith D.DClause (map fst clauses))
    (map snd clauses)

lambdaCase :: [(D.DPat, Q Exp)] -> Q Exp
lambdaCase matches =
  withExpressions
    (D.expToTH . D.dLamCaseE . zipWith D.DMatch (map fst matches))
    (map snd matches)

letBindings :: [(Name, Q Exp)] -> Q Exp -> Q Exp
letBindings [] body = body
letBindings bindings body =
  withExpressions
    (\(result :| values) -> D.expToTH (D.DLetE (zipWith (D.DValD . D.DVarP) (map fst bindings) values) result))
    (body :| map snd bindings)

forallType :: [Name] -> [Q Type] -> Q Type -> Q Type
forallType names constraints body = do
  context <- traverse (>>= D.dsType) constraints
  result <- body >>= D.dsType
  pure (D.typeToTH (D.DForallT (D.DForallInvis (map (`D.DPlainTV` D.SpecifiedSpec) names)) (D.DConstrainedT context result)))

strictField :: Q Type -> Q D.DBangType
strictField ty = do
  declarations <- D.dsDecs =<< [d|data StrictField = StrictField !($ty)|]
  case declarations of
    [D.DDataD _ _ _ _ _ [D.DCon _ _ _ (D.DNormalC _ [field]) _] _] -> pure field
    _ -> fail "unexpected quoted strict field"

-- Do not feed expression bodies through dsExp: it lowers do notation to
-- explicit binds before GHC can apply ApplicativeDo. Sweeten only the outer
-- structure, then fill fresh expression holes with the original quotations.
withExpressions :: (Traversable f, Data a) => (f D.DExp -> a) -> f (Q Exp) -> Q a
withExpressions build expressions = do
  holes <- traverse (\expression -> (,) <$> newName "quotedBody" <*> expression) expressions
  let replacements = [(D.expToTH (D.DVarE name), body) | (name, body) <- toList holes]
  pure (replaceExpressions replacements (build (fmap (D.DVarE . fst) holes)))

replaceExpressions :: (Data a) => [(Exp, Exp)] -> a -> a
replaceExpressions replacements = go
  where
    go :: (Data b) => b -> b
    go node = case cast node >>= (`lookup` replacements) of
      Just body -> fromMaybe node (cast body)
      Nothing -> gmapT go node

-- Obtain native do syntax from quotations, so its constructor shape always
-- matches the host GHC. Inspect only the immediate statement-list field via
-- Data; neither native AST constructors nor CPP are needed. Nested do blocks
-- inside the supplied expressions are left untouched.
quotedStatements :: Q Exp -> Q [Stmt]
quotedStatements expression = do
  body <- expression
  case catMaybes (gmapQ cast body) of
    [statements] -> pure statements
    _ -> fail "unexpected quoted do expression"

bindStatement :: D.DPat -> Q Exp -> Q Stmt
bindStatement pat body = do
  statements <- quotedStatements [|do $(pure (D.patToTH pat)) <- $body; pure ()|]
  case statements of
    first : _ -> pure first
    _ -> fail "missing quoted bind statement"

statement :: Q Exp -> Q Stmt
statement body = do
  statements <- quotedStatements [|do $body|]
  case statements of
    [single] -> pure single
    _ -> fail "unexpected quoted expression statement"

doBlock :: [Q Stmt] -> Q Exp
doBlock [] = fail "cannot generate an empty do block"
doBlock statements = do
  actual <- sequence statements
  template <- [|do pure ()|]
  -- Check the template before replacing its field, to fail explicitly if a
  -- future TH representation no longer has a single statement-list child.
  _ <- quotedStatements (pure template)
  pure (gmapT (\child -> fromMaybe child (cast actual)) template)
