"""Exact identity of the sole admitted structural compiler revision.

The immutable 0.5.8 prerelease build was qualified separately. Its original
candidate selector remains available; only this module selects current admission.
"""
from candidate_profile import (
    VERSION, PIN, ARCHIVE, SOURCE_TREE, EXPORTER, RESOLVER, GHC_VERSION,
    STACK_VERSION, STACK_LOCK, PACKAGES, IG_PIN, IG_ARCHIVE, METADATA_PROBE,
)

# [impl->req~clafer-compiler-capture~1]
# [impl->req~clafer-resolved-import~1]
NAME = "0.5.8"
GENERATION = "clafer-generation/2"
EXPORT_SCHEMA = "generic-aeson-0.5.8/1"
CAPTURE_ENV = "CLAFER_CAPTURE"
