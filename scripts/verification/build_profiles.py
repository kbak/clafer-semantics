"""Explicit build choices; the default import protocol remains compiler_profile."""
import compiler_profile
import candidate_profile
import legacy_profile

PROFILES = {p.NAME: p for p in (compiler_profile, candidate_profile, legacy_profile)}


def select(name):
    try:
        return PROFILES[name]
    except KeyError:
        raise ValueError(f"Unknown compiler build profile: {name}") from None
