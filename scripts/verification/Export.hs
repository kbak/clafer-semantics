{-# LANGUAGE OverloadedStrings #-}
-- Adapter for gsdlab/clafer@6750e6f591b2131549122c13dee94d3d2257eaea.
-- External, unproved extraction code. See docs/resolved-import.md.
module Main where

import Data.Aeson (Value, object, (.=), encode)
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Data (Data, gmapQ, toConstr, showConstr)
import Data.List (isInfixOf, sort, group)
import qualified Data.Map.Strict as M
import qualified Data.StringMap as S
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A
import qualified Language.Clafer.Front.AbsClafer as F
import qualified Language.Clafer.Front.LexClafer as L
import qualified Language.Clafer.Common as G
import qualified Language.Clafer.Intermediate.Intclafer as I
import Language.Clafer.Intermediate.StringAnalyzer (astrModule)
import qualified Observer as Alloy
import Language.Clafer.Generator.Concat (flatten)

-- Enumerating constructor names keeps rejected source forms visible in receipts.
constructors :: Data a => a -> [String]
constructors x = showConstr (toConstr x) : concat (gmapQ constructors x)
inventory :: Data a => a -> [(String, Int)]
inventory = map (\xs -> (head xs, length xs)) . group . sort . constructors

sourceErrors :: F.Module -> [String]
sourceErrors (F.Module _ ds) = concatMap decl ds
  where
  decl (F.ElementDecl _ e) = element e
  decl _ = ["enum"]
  element (F.Subclafer _ c) = clafer c
  element _ = ["non-declaration element"]
  clafer (F.Clafer _ _ temporal _ _ sup ref _ ini trans children) =
    ["temporal modifier" | not (null temporal)] ++ superErrors sup ++ refErrors ref ++
    (case ini of F.InitEmpty _ -> []; _ -> ["initializer"]) ++
    (case trans of F.TransitionEmpty _ -> []; _ -> ["transition"]) ++
    (case children of F.ElementsEmpty _ -> []; F.ElementsList _ es -> concatMap element es)
  superErrors (F.SuperEmpty _) = []
  superErrors (F.SuperSome _ e) = direct e
  refErrors (F.ReferenceEmpty _) = []
  refErrors (F.ReferenceSet _ e) = direct e
  refErrors (F.ReferenceBag _ e) = direct e
  direct (F.ClaferId _ (F.Path _ [F.ModIdIdent _ _])) = []
  direct _ = ["non-direct type expression"]

tokenErrors :: [L.Token] -> [String]
tokenErrors = concatMap audit
  where
  audit (L.PT _ (L.T_PosLineComment s)) = ["source OPTIONS directive" | "//# OPTIONS" `isInfixOf` s]
  audit (L.PT _ (L.T_PosBlockComment _)) = []
  audit _ = ["backend escape or unknown token"]

options :: A.ClaferArgs
options = A.clafer { A.mode = [A.JSON, A.Alloy], A.keep_unused = True,
  A.no_stats = True, A.alloy_mapping = True, A.meta_data = True,
  A.scope_strategy = A.None, A.file = "input.cfr", A.tooldir = "." }

optionsJSON :: A.ClaferArgs -> Value
optionsJSON a = object
  [ "mode" .= map show (A.mode a), "console_output" .= A.console_output a
  , "flatten_inheritance" .= A.flatten_inheritance a, "timeout_analysis" .= A.timeout_analysis a
  , "no_layout" .= A.no_layout a, "new_layout" .= A.new_layout a
  , "check_duplicates" .= A.check_duplicates a, "skip_resolver" .= A.skip_resolver a
  , "keep_unused" .= A.keep_unused a, "no_stats" .= A.no_stats a
  , "validate" .= A.validate a, "tooldir" .= A.tooldir a
  , "alloy_mapping" .= A.alloy_mapping a, "self_contained" .= A.self_contained a
  , "add_graph" .= A.add_graph a, "show_references" .= A.show_references a
  , "add_comments" .= A.add_comments a, "ecore2clafer" .= A.ecore2clafer a
  , "trace_len" .= A.trace_len a, "scope_strategy" .= show (A.scope_strategy a)
  , "afm" .= A.afm a, "meta_data" .= A.meta_data a
  , "minint" .= A.minint a, "maxint" .= A.maxint a
  , "imports" .= A.imports a, "import_root" .= A.import_root a
  , "public_imports" .= A.public_imports a, "import_base" .= A.import_base a
  , "file" .= A.file a ]

-- Observations use the actual generator helpers and the actual consumed map.
observations :: G.GEnv -> I.IModule -> [Value]
observations g m = concatMap (walk []) (G.getSubclafers (I._mDecls m))
  where
  env = Alloy.GenEnv options (G.uidClaferMap g) "for 1"
  walk path c = object
    [ "uid" .= I._uid c
    , "signature" .= I._uid c
    , "fields" .= map flatten (Alloy.genRelations env c)
    , "signature_multiplicity" .= flatten (Alloy.genOptCard c)
    , "parent_fact" .= flatten (Alloy.genParentConst path c)
    , "group_fact" .= flatten (Alloy.genGroupConst env c)
    , "reference_refinement" .= flatten (Alloy.genRefSubrelationConstriant (G.uidClaferMap g) c)
    , "set_uniqueness" .= map flatten (Alloy.genSetUniquenessConstraint c)
    ] : concatMap (walk (I._uid c : path)) (G.getSubclafers (I._elements c))

capture :: String -> Either [C.ClaferErr] Value
capture src = C.runClafer options $ do
  C.addModuleFragment src
  C.parse
  ast <- C.getAst
  parsed <- C.getEnv
  let errors = sourceErrors ast ++ tokenErrors (C.otherTokens parsed)
  if not (null errors) then pure $ object ["status" .= ("unsupported" :: String), "errors" .= errors]
  else do
    raw <- C.desugar (Just "input.cfr")
    C.compile raw
    (im, g, _) <- C.getIr
    env <- C.getEnv
    outputs <- C.generate -- Exactly once, in this analyzed environment.
    let (post, sm) = astrModule im
    case (M.lookup A.JSON outputs, M.lookup A.Alloy outputs) of
      (Just j@C.CompilerResult{}, Just a@C.CompilerResult{}) -> pure $ object
        [ "status" .= ("captured" :: String)
        , "schema" .= ("clafer-generation/1" :: String)
        , "effective_options" .= optionsJSON (C.args env)
        , "backend" .= C.extension a
        , "source_audit" .= object ["errors" .= errors, "constructors" .= inventory ast,
            "tokens" .= map show (C.otherTokens parsed), "ast" .= show ast]
        , "post_analysis" .= im, "post_strings" .= post
        , "strings" .= M.toList sm, "output_strings" .= M.toList (C.stringMap a)
        , "scopes" .= C.scopesList a
        , "consumed_map" .= S.toList (G.uidClaferMap g)
        , "implicit_template" .= S.toList (G.createUidIClaferMap (I.IModule "" []))
        , "observations" .= observations g im
        , "top_fragments" .= map (flatten . Alloy.genDeclaration
            (Alloy.GenEnv (C.args env) (G.uidClaferMap g) "for 1")) (I._mDecls post)
        , "header" .= flatten (Alloy.header (Alloy.GenEnv (C.args env) (G.uidClaferMap g) "for 1") (C.otherTokens env))
        , "json" .= C.outputCode j, "alloy" .= C.outputCode a ]
      _ -> pure $ object ["status" .= ("compiler_rejected" :: String), "errors" .= ["static outputs unavailable" :: String]]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  paths <- getArgs
  case paths of
    [path] -> do
      src <- readFile path
      case capture src of
        Left err -> B.putStrLn $ encode $ object ["status" .= ("compiler_rejected" :: String), "errors" .= [show err]]
        Right value -> B.putStrLn $ encode value
    _ -> fail "usage: clafer-capture input.cfr"
