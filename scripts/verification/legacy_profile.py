"""Historical 0.5.7 build identity; current import admission rejects this revision."""

# [impl->req~clafer-compiler-capture~1]
VERSION = "0.5.7"
PIN = "f6ca5b887d7bacc09915c6fc0278064c8371beac"
ARCHIVE = "51e5c8d47c1e8bf05ca89a8432176c25cb1e6df589aeb36386bcf7627ee3d954"
SOURCE_TREE = "5ed4d4fdc704f198e311e4d6055b59b98789dcf10ff652305c3c863c167f03ca"
EXPORTER = "Export057.hs"
GENERATION = "clafer-generation/2"
EXPORT_SCHEMA = "generic-aeson-0.5.7/1"
STACK_LOCK = {"bytes": 1410, "sha256": "2bed95387bc9ad79df4f70de77a9c7e468125c10a09a68a42da233434b59acff"}

# Build selection is separate from protocol admission.
NAME = "0.5.7"
RESOLVER = "lts-22.44"
GHC_VERSION = "9.6.7"
STACK_VERSION = "3.11.1"
PACKAGES = ("clafer", "aeson", "data-stringmap")
CAPTURE_ENV = "CLAFER_057_CAPTURE"
