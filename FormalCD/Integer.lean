module

public import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Embedding.Basic

/-! # Explicit integer realization and partial singleton extraction

SoSyM §6.1/Figure 21 and Appendix 4 semantics. The interpretation embeds all
mathematical integers. Extraction succeeds exactly on an encoded singleton;
this does not give registry annotations an implicit primitive-domain meaning.
-/

@[expose] public section
universe u
namespace FormalCD

-- [impl->req~formalcd-integer-realization~1]
structure IntegerRealization (U : Type u) where
  encode : Int ↪ U
  decode : U → Int
  decode_encode : ∀ n, decode (encode n) = n

def IntegerRealization.domain {U : Type u} (R : IntegerRealization U) : Set U :=
  Set.range R.encode

namespace IntegerRealization
variable {U : Type u} (R : IntegerRealization U)

/-- A successful result is exactly one realized integer object. -/
def Extracts (values : Set U) (n : Int) : Prop := values = {R.encode n}

/-- Object uniqueness and domain membership are separate runtime hypotheses. -/
def WellDefined (values : Set U) : Prop :=
  ∃ x, values = {x} ∧ x ∈ R.domain

theorem encode_decode {x : U} (h : x ∈ R.domain) : R.encode (R.decode x) = x := by
  obtain ⟨n, rfl⟩ := h
  rw [R.decode_encode]

theorem extracts_unique {values : Set U} {m n : Int}
    (hm : R.Extracts values m) (hn : R.Extracts values n) : m = n := by
  apply R.encode.injective
  exact Set.singleton_injective (hm.symm.trans hn)

theorem wellDefined_iff (values : Set U) :
    R.WellDefined values ↔ ∃ n, R.Extracts values n := by
  constructor
  · rintro ⟨x, hx, hd⟩
    exact ⟨R.decode x, hx.trans (congrArg (fun z : U => ({z} : Set U)) (R.encode_decode hd).symm)⟩
  · rintro ⟨n, hn⟩
    exact ⟨R.encode n, hn, ⟨n, rfl⟩⟩

/-- The only chosen witness is proved unique by `extracts_unique`.
Invalid collections return none; decode outside the integer domain is never used. -/
noncomputable def extract (values : Set U) : Option Int := by
  classical
  exact if h : ∃ n, R.Extracts values n then some (Classical.choose h) else none

-- [proof->req~formalcd-integer-realization~1]
theorem extract_eq_some_iff (values : Set U) (n : Int) :
    R.extract values = some n ↔ R.Extracts values n := by
  classical
  unfold extract
  split
  · rename_i h
    constructor
    · intro he
      cases Option.some.inj he
      exact Classical.choose_spec h
    · intro hn
      exact congrArg some (R.extracts_unique (Classical.choose_spec h) hn)
  · rename_i h
    constructor
    · intro he; cases he
    · intro hn; exact (h ⟨n, hn⟩).elim

theorem extract_none_iff (values : Set U) :
    R.extract values = none ↔ ¬ R.WellDefined values := by
  classical
  rw [R.wellDefined_iff]
  unfold extract
  split <;> simp_all

@[simp] theorem extract_encoded (n : Int) : R.extract {R.encode n} = some n :=
  (R.extract_eq_some_iff _ _).mpr rfl

@[simp] theorem extract_empty : R.extract ∅ = none := by
  apply (R.extract_none_iff _).mpr
  rintro ⟨x, hx, _⟩
  have : x ∈ (∅ : Set U) := hx.symm ▸ Set.mem_singleton x
  exact this

theorem extract_multiple {values : Set U} {x y : U}
    (hx : x ∈ values) (hy : y ∈ values) (hne : x ≠ y) : R.extract values = none := by
  apply (R.extract_none_iff _).mpr
  rintro ⟨z, rfl, _⟩
  exact hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)

theorem extract_wrong_domain {x : U} (hx : x ∉ R.domain) : R.extract {x} = none := by
  apply (R.extract_none_iff _).mpr
  rintro ⟨y, he, hy⟩
  exact hx ((Set.singleton_injective he).symm ▸ hy)

/-- The domain is in correspondence with Int, not with a finite candidate list. -/
def objectEquiv : R.domain ≃ Int where
  toFun x := R.decode x.val
  invFun n := ⟨R.encode n, ⟨n, rfl⟩⟩
  left_inv x := Subtype.ext (R.encode_decode x.property)
  right_inv := R.decode_encode

end IntegerRealization

end FormalCD
