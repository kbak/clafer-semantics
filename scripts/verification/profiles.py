"""Exact compiler identities; schema selection never depends on document shape."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Profile:
    version: str
    commit: str
    archive: str
    source_tree: str
    exporter: str
    generation: str

    @property
    def export_schema(self):
        return f"generic-aeson-{self.version}/1"

    @property
    def modern(self):
        return self == CURRENT


# [impl->req~clafer-compiler-capture~1]
LEGACY = Profile("0.5.4", "6750e6f591b2131549122c13dee94d3d2257eaea",
    "2b9e111e21d979ff331816161738df9b07417658f788e0939f31b84292cae74f",
    "4312978c73cf593e7d12f02fc705b68e5b6e11e16da1ace08cb0ab40932f3a99",
    "Export.hs", "clafer-generation/1")
CURRENT = Profile("0.5.7", "f6ca5b887d7bacc09915c6fc0278064c8371beac",
    "51e5c8d47c1e8bf05ca89a8432176c25cb1e6df589aeb36386bcf7627ee3d954",
    "5ed4d4fdc704f198e311e4d6055b59b98789dcf10ff652305c3c863c167f03ca",
    "Export057.hs", "clafer-generation/2")
PROFILES = (LEGACY, CURRENT)
STACK_LOCK = {"bytes": 1410, "sha256": "2bed95387bc9ad79df4f70de77a9c7e468125c10a09a68a42da233434b59acff"}


def by_commit(commit):
    return next((p for p in PROFILES if p.commit == commit), None)


def by_version(version):
    return next((p for p in PROFILES if p.version == version), None)
