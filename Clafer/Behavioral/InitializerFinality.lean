module

public import Clafer.Behavioral.InitializerStructure

/-! # Initialization and final references within each lifetime

Behavioral §5 Definitions 3–5 / §6.1 and #171's accepted finality correction.
`finalref` fixes a target, not a changing or later undefined RHS observation.
The equivalence is for per-instance clocks and uninterrupted lives only.
-/

@[expose] public section
namespace Clafer.Behavioral.Initializers.Finality
universe u
variable {C : Type} {U : Type u}

-- [proof->req~behavioral-modifiers~1]
theorem live_has_birth (τ : Trace C U) (t : Nat) (x : U) (present : x ∈ τ.live t) :
    ∃ b, b ≤ t ∧ τ.Starts b x ∧ Lifetime.Through (fun j => x ∈ τ.live j) b t := by
  classical
  induction t with
  | zero => exact ⟨0, le_rfl, (τ.starts_zero x).mpr present, fun j _ hj =>
      (Nat.eq_zero_of_le_zero hj) ▸ present⟩
  | succ t ih =>
    by_cases prev : x ∈ τ.live t
    · obtain ⟨b, bt, birth, life⟩ := ih prev
      refine ⟨b, by omega, birth, ?_⟩
      intro j bj jt
      rcases eq_or_lt_of_le jt with rfl | earlier
      · exact present
      · exact life j bj (by omega)
    · exact ⟨t + 1, le_rfl, (τ.starts_succ t x).mpr ⟨present, prev⟩,
        fun j hj h' => (Nat.le_antisymm h' hj) ▸ present⟩

def Every (heads : Nat → Set U) (target : Nat → U → U)
    (rhs : Nat → U → Option (Set U)) : Prop :=
  ∀ t x, x ∈ heads t → rhs t x = some {target t x}

-- [proof->req~behavioral-modifiers~1]
/-- On an initialized lifetime with fixed target q, later equality is exactly
an additional demand that the original RHS remain defined and equal to q. -/
theorem within_lifetime (τ : Trace C U) (target : Nat → U → U)
    (rhs : Nat → U → Option (Set U)) (x : U) (b t : Nat) (bt : b ≤ t)
    (life : Lifetime.Through (fun j => x ∈ τ.live j) b t)
    (fixed : Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => target j x))
    (initialized : rhs b x = some {target b x}) :
    rhs t x = some {target t x} ↔ rhs t x = rhs b x := by
  have eq : target b x = target t x := fixed b t bt life
  rw [← eq, initialized]

/-- Sufficient and explicit observation stability, local to each life. The
head membership premise expresses the fixed resolved declaration identity. -/
theorem births_iff_every (τ : Trace C U) (heads : Nat → Set U)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U))
    (live : ∀ t, heads t ⊆ τ.live t)
    (sameDeclaration : ∀ i j x, x ∈ heads i → x ∈ τ.live j → x ∈ heads j)
    (fixed : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => target j x))
    (stableRhs : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => rhs j x)) :
    Candidate.SingleBirths τ heads target rhs ↔ Every heads target rhs := by
  constructor
  · intro init t x hx
    obtain ⟨b, bt, birth, life⟩ := live_has_birth τ t x (live t hx)
    have hb := init b x (sameDeclaration t b x hx birth.1) birth
    have er : rhs b x = rhs t x := stableRhs x b t bt life
    have et : target b x = target t x := fixed x b t bt life
    rw [← er, ← et]
    exact hb
  · intro eq t x hx _
    exact eq t x hx

/-- Adding an independent head-stability requirement to both sides preserves
this equivalence; it does not discharge the RHS-stability premise. -/
theorem with_head_stability (headStable : Prop) (τ : Trace C U) (heads : Nat → Set U)
    (target : Nat → U → U) (rhs : Nat → U → Option (Set U))
    (live : ∀ t, heads t ⊆ τ.live t)
    (sameDeclaration : ∀ i j x, x ∈ heads i → x ∈ τ.live j → x ∈ heads j)
    (fixed : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => target j x))
    (stableRhs : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => rhs j x)) :
    (headStable ∧ Candidate.SingleBirths τ heads target rhs) ↔
      (headStable ∧ Every heads target rhs) :=
  and_congr Iff.rfl (births_iff_every τ heads target rhs live sameDeclaration fixed stableRhs)

-- [proof->req~behavioral-modifiers~1]
theorem target_stable {k : Nat} (m : Structural.Core k) (τ : Trace (Fin k) U)
    (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (final : Modifiers.FinalRef m τ d) (x : U) :
    Modifiers.Stable (fun t => x ∈ τ.live t) (fun t => Structure.target m τ valid owner t x) := by
  intro i j ij life
  by_cases typed : m.toEffectiveCore.Ancestor (τ.identities.directType x) d
  · have hi : x ∈ (τ.raw m.toEffectiveCore i).head d := ⟨life i le_rfl ij, typed⟩
    have hj : x ∈ (τ.raw m.toEffectiveCore j).head d := ⟨life j ij le_rfl, typed⟩
    have same : {y | (Structural.current m τ i).deref d x y} =
        {y | (Structural.current m τ j).deref d x y} := final x typed i j ij life
    rw [Structure.target_singleton m τ valid owner i x hi,
      Structure.target_singleton m τ valid owner j x hj] at same
    exact Set.singleton_injective same
  · have absent (t : Nat) : x ∉ (τ.raw m.toEffectiveCore t).head d := fun h => typed h.2
    simp only [Structure.target, dite_eq_right (absent i), dite_eq_right (absent j)]

theorem finalref_equivalence {k : Nat} (m : Structural.Core k) (τ : Trace (Fin k) U)
    (valid : Structural.Valid m τ) {d o : Fin k}
    (owner : InheritedReference.Owner m.family d o) (final : Modifiers.FinalRef m τ d)
    (rhs : Nat → U → Option (Set U))
    (stableRhs : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j) (fun j => rhs j x)) :
    Candidate.SingleBirths τ (fun t => (τ.raw m.toEffectiveCore t).head d)
      (Structure.target m τ valid owner) rhs ↔
    Every (fun t => (τ.raw m.toEffectiveCore t).head d)
      (Structure.target m τ valid owner) rhs :=
  births_iff_every τ _ _ rhs (fun _ _ h => h.1)
    (fun _ _ _ h live => ⟨live, h.2⟩) (target_stable m τ valid owner final) stableRhs

-- [proof->req~behavioral-modifiers~1]
/-- Production `:=` and aggregate `=` agree under finalref and stable original
RHS observations, on the independently admitted singleton/scalar domain. -/
theorem production_equivalence {k : Nat} {U : Type u} {V : Type}
    (m : Structural.Core k) (τ : Trace (Fin k) U) (valid : Structural.Valid m τ)
    {d o : Fin k} (owner : InheritedReference.Owner m.family d o)
    (final : Modifiers.FinalRef m τ d) (source : V → Transport.Value U (Set U) 0) (rhs : V)
    (admission : ∀ t p, p ∈ Structure.contexts m τ d t →
      (Structure.heads m τ d t p).Subsingleton ∨
        ∀ S, source rhs (.closed p) t = some S → S.Subsingleton)
    (stableRhs : ∀ x, Modifiers.Stable (fun j => x ∈ τ.live j)
      (fun j => (Transport.original τ.identities (Structure.origin m d) x).bind
        (fun p => source rhs (.closed p) j))) :
    Meaning τ (Structure.view m τ valid owner) source
        ⟨d, Structure.origin m d, .instanceBirth, rhs⟩ ↔
      Meaning τ (Structure.view m τ valid owner) source
        ⟨d, Structure.origin m d, .everyLive, rhs⟩ :=
  (finalref_equivalence m τ valid owner final _ stableRhs).trans
    (Structure.every_fibers m τ valid owner source rhs admission).symm

end Clafer.Behavioral.Initializers.Finality
