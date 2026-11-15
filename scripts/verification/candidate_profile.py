"""Immutable 0.5.8 release build; the candidate selector is retained as an alias."""

# [impl->req~clafer-resolved-import~1]
NAME = "0.5.8-candidate"
VERSION = "0.5.8"
PIN = "dbc06d37ef23eb9186d1016e3bf678858621e92d"
ARCHIVE = "cce8e723fce067687ec9434682b445edc364698dece8fdf49d22b8184bde413c"
SOURCE_TREE = "d6822ede588ed020045e1630872c186361b61aa6538c64198da1cf2edc4ac0a1"
EXPORTER = "Export.hs"
RESOLVER = "nightly-2026-11-11"
GHC_VERSION = "9.12.4"
STACK_VERSION = "3.11.1"
STACK_LOCK = {"bytes": 474, "sha256": "4176b38a3b52684cb49761cfa8f98ee251c3a82ed6f03ce7c80c45125dc67b32"}
PACKAGES = ("clafer", "aeson", "containers")
CAPTURE_ENV = "CLAFER_058_CAPTURE"

# The JSON probe compiles the unchanged IG encoding/model modules, not its solver.
IG_PIN = "7942789d84939e98da38d4219cefbbd5b9e0d184"
IG_ARCHIVE = "bf8e409c6612d81545eb300a7773448faa35b1ccd20d61875f66fba73e903cdd"
METADATA_PROBE = "Metadata.hs"
