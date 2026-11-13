{-# LANGUAGE OverloadedStrings #-}
-- Boundary probe for the pinned compiler and claferIG encoders. No solver runs.
module Main where

import Data.Aeson (Value, object, (.=), encode)
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Maybe (fromJust)
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A
import qualified Language.Clafer.Common as G
import qualified Language.Clafer.Intermediate.Intclafer as I
import qualified Language.Clafer.JSONMetaData as J
import qualified Language.Clafer.QNameUID as Q
import qualified Language.Clafer.IG.JSONGenerator as IG
import qualified Language.Clafer.IG.ClaferModel as M

metadata :: I.IModule -> Value
metadata im = object
  [ "name_map" .= J.generateJSONnameUIDMap names
  , "scopes" .= J.generateJSONScopes names scopes
  , "triples" .= triples
  , "scope_input" .= scopes ]
  where
  names = Q.deriveQNameMaps im
  triples = Q.getQNameUIDTriples names
  scopes = [(uid, n) | ((_, _, uid), n) <- zip triples [0..]]

-- Exercise escaping beyond what the source identifier grammar permits. These
-- are encoder inputs, not admitted Clafer models or finite-checker instances.
synthetic :: Value
synthetic = object
  [ "metadata" .= metadata im
  , "instance" .= IG.generateJSON registry instanceModel
  , "empty_instance" .= IG.generateJSON registry (M.ClaferModel [])
  , "empty_metadata" .= metadata (I.IModule "" []) ]
  where
  root = fromJust $ G.findIClafer (G.createUidIClaferMap (I.IModule "" [])) "root"
  base = root { I._ident = "Base", I._uid = "Base", I._elements = [] }
  name = "quote\"slash\\tab\tline\nreturn\rback\bform\fctrl\SOHÉ\x1f642"
  owner = root { I._ident = name, I._uid = "Owner", I._parentUID = "root",
    I._super = Just $ G.pExpDefPidPos $ I.IClaferId "" "Base" True $ I.GlobalBind "Base",
    I._card = Just (0, -1), I._elements = [I.IEClafer child] }
  child = root { I._ident = "child'", I._uid = "child", I._parentUID = "Owner",
    I._reference = Just $ I.IReference False [] $ G.pExpDefPidPos $
      I.IClaferId "" "Base" True $ I.GlobalBind "Base",
    I._elements = [] }
  im = I.IModule "" [I.IEClafer base, I.IEClafer owner]
  registry = G.createUidIClaferMap im
  instanceModel = M.ClaferModel
    [M.Clafer (M.Id "Owner$0" 0) "Owner" Nothing
      [M.Clafer (M.Id "child$0" 0) "child" (Just $ M.AliasValue $ M.Id ("target\"\\\t\nÉ" ++ "$1") 1) []],
     M.Clafer (M.Id "Base$0" 0) "Base" (Just $ M.IntValue (-17)) []]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  case args of
    ["--synthetic"] -> B.putStrLn $ encode synthetic
    [path] -> do
      src <- readFile path
      let result = C.runClafer A.clafer{A.keep_unused = True, A.file = "input.cfr"} $ do
            C.addModuleFragment src
            C.parse
            raw <- C.desugar (Just "input.cfr")
            C.compile raw
            (im, _, _) <- C.getIr
            pure $ metadata im
      case result of
        Left err -> fail (show err)
        Right value -> B.putStrLn $ encode value
    _ -> fail "usage: metadata-probe input.cfr | --synthetic"
