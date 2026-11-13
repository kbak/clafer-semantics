"""Build-only 0.5.8 qualification; this does not change protocol admission."""

# [impl->req~clafer-resolved-import~1]
NAME = "0.5.8-candidate"
VERSION = "0.5.8"
PIN = "fca0deb9c766261f5c0d2ae57af4ba9b07e1279a"
ARCHIVE = "fcf7bf883723e7eb22ff2f3c1b6538f0c967cb5eace3a00a89f5fcd2e4a4edc5"
SOURCE_TREE = "c9009d0fa8fb3d834b307b6d481a0ac99aa02994ac65200a3f25a0391281be8a"
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
