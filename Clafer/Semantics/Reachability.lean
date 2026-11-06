module

public import Clafer.Semantics.Structural
public import Mathlib.Data.Finset.Max

-- [proof->req~clafer-structural-satisfaction~1]

/-!
# Derived containment reachability

SoSyM §5.3.4–5/§5.4–5 under the guarded finite declaration fragment.
Abstract cover follows subtype identities until a concrete membership exists;
concrete parent ownership then reaches the singleton root. Neither reference
edges nor a global disjointness assumption enter this argument.
-/

@[expose] public section
namespace Clafer.Semantics
open MCS

namespace Configuration
variable {n : Nat} {U : Type} {m : EffectiveCore n} {s : Configuration (Fin n) U}

theorem concrete_member (wf : m.WellFormed) (ha : s.Abstracts m)
    {d : Fin n} {x : U} (hx : (x ∈ s.head d)) :
    ∃ c, (x ∈ s.head c) ∧ m.family.isAbstract c = false := by
  classical
  obtain ⟨rank, hr⟩ := wf.1.super_rank
  let members := Finset.univ.filter (fun c => (x ∈ s.head c))
  obtain ⟨c, hc, hmax⟩ := members.exists_max_image rank
    ⟨d, by simp [members, hx]⟩
  have hc' : (x ∈ s.head c) := (Finset.mem_filter.mp hc).2
  refine ⟨c, hc', ?_⟩
  cases hab : m.family.isAbstract c with
  | false => rfl
  | true =>
    obtain ⟨e, he, hex⟩ := (ha c hab).1 x hc'
    have hle := hmax e (by simp [members, hex])
    have hlt := hr e c he
    omega

/-- Coverage descends from the particular abstract head, not an unrelated
membership. Finite super rank rules out infinite abstract-only descent. -/
theorem concrete_descendant (wf : m.WellFormed) (ha : s.Abstracts m)
    {d : Fin n} {x : U} (hx : x ∈ s.head d) :
    ∃ c, x ∈ s.head c ∧ m.family.isAbstract c = false ∧
      Relation.ReflTransGen (fun c s => m.family.super c = some s) c d := by
  classical
  obtain ⟨rank, hr⟩ := wf.1.super_rank
  let members := Finset.univ.filter (fun c => x ∈ s.head c ∧
    Relation.ReflTransGen (fun c s => m.family.super c = some s) c d)
  obtain ⟨c, hc, hmax⟩ := members.exists_max_image rank
    ⟨d, by simp only [members, Finset.mem_filter, Finset.mem_univ, true_and];
           exact ⟨hx, Relation.ReflTransGen.refl⟩⟩
  have hc' := (Finset.mem_filter.mp hc).2
  refine ⟨c, hc'.1, ?_, hc'.2⟩
  cases hab : m.family.isAbstract c with
  | false => rfl
  | true =>
    obtain ⟨e, he, hex⟩ := (ha c hab).1 x hc'.1
    have hep := Relation.ReflTransGen.head (r := fun c s => m.family.super c = some s) he hc'.2
    have hle := hmax e (by simp [members, hex, hep])
    have hlt := hr e c he
    omega

theorem unused_abstract_empty (wf : m.WellFormed) (ha : s.Abstracts m)
    {d : Fin n} (hd : m.family.isAbstract d = true)
    (unused : ∀ c, m.family.isAbstract c = false →
      ¬ Relation.TransGen (fun c s => m.family.super c = some s) c d) :
    s.head d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨c, _, hc, path⟩ := s.concrete_descendant wf ha hx
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with he | he
  · subst c; simp [hd] at hc
  · exact unused c hc he

theorem concrete_reaches (wf : m.WellFormed) (support : m.Supported)
    (typed : s.Typed m) (rooted : s.Rooted m) (parents : s.Parents m)
    {d : Fin n} {x : U} (hx : (x ∈ s.head d)) (hd : m.family.isAbstract d = false) :
    s.Reaches x := by
  obtain ⟨depth, hr⟩ := wf.1.parent_rank
  have go : ∀ k, ∀ d, depth d = k → ∀ x, (x ∈ s.head d) →
      m.family.isAbstract d = false → s.Reaches x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hdepth x hx hd
      by_cases hroot : d = m.family.root
      · subst d
        have he := (rooted.1 x).mp hx
        subst x
        exact Relation.ReflTransGen.refl
      · cases hp : m.family.parent d with
        | none =>
          have h := wf.1.parentless_abstract d hp hroot
          simp [hd] at h
        | some p =>
          obtain ⟨y, hy, _⟩ := parents d p hp x hx
          obtain ⟨_, c, hc, hcy⟩ := typed.1 d y x hy
          have he : c = p := Option.some.inj (hc.symm.trans hp)
          subst c
          have hpa : m.family.isAbstract p = false := by
            cases ha : m.family.isAbstract p with
            | false => rfl
            | true => exact ((support.2.1 p ha).2.2.1 d hp).elim
          have hyreach := ih (depth p) (by have := hr d p hp; omega) p rfl y hcy hpa
          exact hyreach.tail ⟨d, hy⟩
  exact go (depth d) d rfl x hx hd

end Configuration

theorem structural_reaches {n : Nat} {U : Type} {m : EffectiveCore n}
    {s : Configuration (Fin n) U} (wf : m.WellFormed) (support : m.Supported)
    (h : StructuralSatisfies m s) (x : U) : s.Reaches x := by
  rcases h.2.1.2.2 x with he | ⟨d, _, hd⟩
  · subst x
    exact Relation.ReflTransGen.refl
  · obtain ⟨c, hc, ha⟩ := s.concrete_member wf h.2.2.2.1 hd
    exact s.concrete_reaches wf support h.1 h.2.1 h.2.2.2.2.1 hc ha

end Clafer.Semantics
