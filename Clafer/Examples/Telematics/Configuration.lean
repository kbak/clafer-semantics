module

public import Clafer.Examples.Telematics.Input

/-!
[impl->req~clafer-appendix-f-complete~1]
[proof->req~clafer-appendix-f-complete~1]
-/

/-!
# Concrete telematics configuration

SoSyM Appendix 6 PDF p.34. Two ECUs each own two displays; versions are 2 for
ECUs and 3 for displays. Every represented mathematical integer is contained
by the actual root. Finite nonprimitive heads remain separate from that domain.
-/

@[expose] public section
namespace Clafer.Examples.Telematics
open CategoryTheory MCS Compile DPGraph DPGraph.Predicates Semantics Constraints

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

abbrev U := Sum (Fin 36) Int
abbrev atom (n : Fin 36) : U := Sum.inl n

def integers : IntegerRealization U where
  encode := ⟨Sum.inr, Sum.inr_injective⟩
  decode | .inl _ => 0 | .inr i => i
  decode_encode _ := rfl

def heads : Fin 28 → Finset (Fin 36) :=
  ![{0}, {1}, {2}, {29}, {30}, {31}, ∅, {32}, {33}, {34}, ∅, {35}, ∅,
    {17,18,19,20}, {21,22,23,24}, ∅, {25,26,27,28}, ∅, ∅, ∅,
    {1,2,3,4,5,6}, {7,8,9,10,11,12}, {1,2}, {3,4,5,6},
    {13,14,15,16}, {17,18,19,20}, {1,2}, {3,4,5,6}]

def ownership : Fin 28 → Finset (Fin 36 × Fin 36) :=
  ![∅, {(0,1)}, {(0,2)}, {(2,29)}, {(0,30)}, {(30,31)}, ∅,
    {(31,32)}, {(30,33)}, {(30,34)}, ∅, {(34,35)}, ∅, ∅,
    {(17,21),(18,22),(19,23),(20,24)}, ∅,
    {(21,25),(22,26),(23,27),(24,28)}, ∅, ∅, ∅, ∅,
    {(1,7),(2,8),(3,9),(4,10),(5,11),(6,12)}, ∅, ∅,
    {(3,13),(4,14),(5,15),(6,16)}, {(3,17),(4,18),(5,19),(6,20)}, ∅,
    {(1,3),(1,4),(2,5),(2,6)}]

def targets : Fin 28 → Finset (Fin 36 × Fin 36) :=
  ![∅, ∅, ∅, {(29,1)}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅,
    ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {(13,1),(14,1),(15,2),(16,2)}, ∅, ∅, ∅]

def config : Configuration (Fin 28) U where
  root := atom 0
  head d := {x | match x with
    | .inl n => n ∈ heads d
    | .inr _ => d = 12}
  contains d p x := match p, x with
    | .inl a, .inl b => (a,b) ∈ ownership d
    | .inl a, .inr _ => d = 12 ∧ a = 0
    | _, _ => False
  deref d x t := match x, t with
    | .inl a, .inl b => (a,b) ∈ targets d
    | .inl a, .inr v => d = 21 ∧ a ∈ heads 21 ∧ v = (if a = 7 ∨ a = 8 then 2 else 3)
    | _, _ => False

theorem integer_extent : config.head 12 = integers.domain := by
  ext x
  cases x <;> simp [config, heads, FormalCD.IntegerRealization.domain, integers]

theorem primitive_root_containment (v : Int) : config.contains 12 config.root (integers.encode v) :=
  ⟨rfl,rfl⟩

theorem nonprimitive_finite (d : Fin 28) (hd : d ≠ 12) : (config.head d).Finite := by
  have he : config.head d = Sum.inl '' (heads d : Set (Fin 36)) := by
    ext x
    cases x <;> simp [config, hd]
  rw [he]
  exact (heads d).finite_toSet.image Sum.inl

theorem typed : config.Typed core.toEffectiveCore := by
  constructor
  · intro d p x
    cases p with
    | inr p => simp [config]
    | inl p =>
      cases x with
      | inr x => fin_cases d <;> simp [config, parents_eq, Telematics.Structural.parents, heads]
      | inl x =>
        fin_cases d <;> simp [config, heads, ownership, parents_eq, Telematics.Structural.parents]
        all_goals aesop
  · intro d x t
    cases x with
    | inr x => simp [config]
    | inl x =>
      cases t with
      | inr t =>
        fin_cases d <;> simp [config, references_eq, Telematics.Structural.references, ReferenceTo.target]
        intro h _; exact h
      | inl t =>
        fin_cases d <;> simp [config, heads, targets, references_eq,
          Telematics.Structural.references, ReferenceTo.target]
        all_goals aesop

theorem inherits : config.Inherits core.toEffectiveCore := by
  intro d c hc x hx
  rw [supers_eq] at hc
  fin_cases d <;> simp [Telematics.Structural.supers] at hc
  all_goals subst c; cases x <;> simp_all [config, heads]
  all_goals aesop

theorem parents_hold : config.Parents core.toEffectiveCore := by
  intro d p hp x hx
  rw [parents_eq] at hp
  cases x with
  | inr v =>
    simp only [config] at hx
    subst d
    refine ⟨atom 0, ⟨rfl,rfl⟩, ?_⟩
    intro y hy
    cases y <;> simp_all [config]
  | inl x =>
    fin_cases d <;> simp [Telematics.Structural.parents] at hp
    all_goals simp [config, heads] at hx
    all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [config, ownership, ExistsUnique, Sum.forall]

theorem references_hold : config.References core.toEffectiveCore := by
  intro d t ht x hx
  rw [references_eq] at ht
  fin_cases d <;> simp [Telematics.Structural.references, ReferenceTo.target] at ht
  all_goals cases x
  all_goals simp [config, heads] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [config, targets, heads, ExistsUnique, Sum.forall]

theorem keys : config.Keys core.toEffectiveCore := by
  intro d hd
  rw [references_eq] at hd
  fin_cases d <;> simp [Telematics.Structural.references, ReferenceTo.kind] at hd
  all_goals intro p t x y
  all_goals cases p <;> cases t <;> cases x <;> cases y
  all_goals simp [config, ownership, targets, heads]
  all_goals aesop

theorem abstracts : Semantics.Realization.Abstracts core config := by
  intro d hd
  rw [explicit_eq] at hd
  fin_cases d <;> simp [Telematics.Structural.explicit] at hd
  all_goals simp only [supers_eq]
  all_goals simp [config, Sum.forall]
  all_goals decide

theorem rooted : config.Rooted core.toEffectiveCore := by
  change config.Rooted {core.toEffectiveCore with family.root := (0 : Fin 28)}
  unfold Configuration.Rooted
  simp only [config, Sum.forall]
  constructor
  · simp [heads]
  · constructor
    · intro d hd; fin_cases d <;> simp_all [heads]
    · constructor
      · decide
      · intro v; exact Or.inr ⟨12, by decide, rfl⟩



theorem unrestricted_range (A : Type) : InRange unrestricted A :=
  ⟨⟨⟨Fin.elim0, fun x => Fin.elim0 x⟩⟩, trivial⟩

def finiteFiber (d : Fin 28) (hd : d ≠ 12) (a : Fin 36) :
    {x : U // config.contains d (atom a) x} ≃ {b : Fin 36 // (a,b) ∈ ownership d} where
  toFun x := match x with
    | ⟨.inl b, hb⟩ => ⟨b,hb⟩
    | ⟨.inr _, hb⟩ => False.elim (hd hb.1)
  invFun b := ⟨atom b.val,b.property⟩
  left_inv x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | inl b => rfl
    | inr v => exact (hd hx.1).elim
  right_inv _ := rfl

theorem multiplicities : config.Multiplicities core.toEffectiveCore := by
  intro d p hp x hx
  rw [parents_eq] at hp
  rw [bounds_eq]
  by_cases hd : d = 12
  · subst d; exact unrestricted_range _
  · rw [bounds, ite_eq_right hd]
    cases x with
    | inr v =>
      have he : p = 12 := hx
      subst p
      fin_cases d <;> simp [Telematics.Structural.parents] at hp
    | inl x =>
      apply (inRange_iff _ (finiteFiber d hd x)).mpr
      rw [DPGraph.Predicates.inRange_card]
      fin_cases d <;> try { exact (hd rfl).elim }
      all_goals simp [Telematics.Structural.parents] at hp
      all_goals subst p
      all_goals simp [config, heads] at hx
      all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide

theorem ancestor_iff (p a : Fin 28) : Compile.Groups.Ancestor core.family p a ↔
    a ∈ Telematics.Structural.ancestorTable p := by
  have he : core.family.super = Telematics.Structural.core.family.super := by
    funext d; rw [supers_eq, Telematics.Structural.supers_eq]
  simpa only [Compile.Groups.Ancestor, he] using Telematics.Structural.ancestor_iff p a

theorem channel_children (c : Fin 28) : Telematics.Structural.parents c = some 5 ↔ c = 6 ∨ c = 7 := by
  fin_cases c <;> decide

theorem telematics_size_children (c : Fin 28) : Telematics.Structural.parents c = some 9 ↔ c = 10 ∨ c = 11 := by
  fin_cases c <;> decide

theorem options_size_children (c : Fin 28) : Telematics.Structural.parents c = some 14 ↔ c = 15 ∨ c = 16 := by
  fin_cases c <;> decide

theorem range_one_of_unique (P : U → Prop) (h : ∃! x, P x) : InRange one {x // P x} := by
  obtain ⟨x,hx,hu⟩ := h
  apply (Semantics.inRange_one_iff _).mpr
  refine ⟨⟨⟨x,hx⟩⟩, ⟨?_⟩⟩
  intro a b
  apply Subtype.ext
  exact (hu a.val a.property).trans (hu b.val b.property).symm

/-- The root can have infinitely many primitive children: its unrestricted
range does not invoke a finite cardinality evaluator. -/
theorem groups : Semantics.Realization.Groups core config := by
  intro d hd x
  rw [family_groups]
  by_cases he : d = 5 ∨ d = 9 ∨ d = 14
  · rcases x with ⟨x,hx⟩
    rcases he with rfl | rfl | rfl
    all_goals cases x with
    | inr v => simp [config] at hx
    | inl x =>
      simp [config, heads] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        change InRange one _
        apply range_one_of_unique
        simp [ExistsUnique, Compile.Groups.ChildObjects, ancestor_iff,
          Telematics.Structural.ancestorTable, parents_eq, channel_children, telematics_size_children,
          options_size_children, config, ownership, Sum.forall]
  · have hb : Telematics.Structural.groupBounds d = unrestricted := by
      fin_cases d <;> simp_all [Telematics.Structural.groupBounds]
    rw [hb]
    exact unrestricted_range _

theorem declaration_disjoint : config.DeclarationDisjoint core.toEffectiveCore := by
  change ∀ d e x, x ∈ config.head d → x ∈ config.head e →
    Compile.Groups.Ancestor core.family d e ∨ Compile.Groups.Ancestor core.family e d
  simp only [ancestor_iff]
  intro d e x
  cases x with
  | inl x =>
    change x ∈ heads d → x ∈ heads e → _
    revert d e x
    decide
  | inr v =>
    simp only [config, Set.mem_ofPred_eq]
    intro hd he
    subst d; subst e
    decide

theorem structural_satisfaction : Semantics.Realization.Satisfies core config :=
  ⟨typed, rooted, ⟨inherits, parents_hold, references_hold, keys, multiplicities⟩,
    abstracts, groups, declaration_disjoint⟩

end Clafer.Examples.Telematics
