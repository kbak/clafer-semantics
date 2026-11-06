module

public import Clafer.Examples.Telematics.Expressions
public import Clafer.Constraints.CollectionMeaning
public import Clafer.Constraints.DenotationDefined

/-! # Definedness from admissible telematics environments

SoSyM Appendix 6 (PDF p.34).

The finite structural extents are separate from the infinite primitive domain.
The numeric comparison consumes exactly the delivered version/server bounds.
-/

@[expose] public section
universe u w
namespace Clafer.Examples.Telematics.Definedness
open Clafer.Constraints Telematics.Expressions CategoryTheory DPGraph.Predicates

variable {U : Type u}

-- [impl->req~clafer-appendix-f-expressions~1]
def FiniteStructural {c} (m : IntegerBinding.{u,w} (support c) U) : Prop :=
  ∀ x : Fin 28, x ≠ 27 → (m.model.obj x : Set U).Finite

theorem some_defined {c x} (m : IntegerBinding.{u,w} (support c) U)
    (ρ : Environment (support c) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m)
    (e : Expr (support c) [] (.collection (.objects x))) (hx : x ≠ 27) :
    e.some.Defined m ρ :=
  (show (Expr.integer 0 : Expr (support c) [] _).Defined m ρ from ⟨⟨0⟩,rfl⟩).less
    (e.cardinality_objects_defined m ρ hρ (hf x hx))

theorem no_defined {c x} (m : IntegerBinding.{u,w} (support c) U)
    (ρ : Environment (support c) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m)
    (e : Expr (support c) [] (.collection (.objects x))) (hx : x ≠ 27) :
    e.no.Defined m ρ :=
  (e.cardinality_objects_defined m ρ hρ (hf x hx)).equal ⟨⟨0⟩,rfl⟩

theorem two_defined {c x} (m : IntegerBinding.{u,w} (support c) U)
    (ρ : Environment (support c) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m)
    (e : Expr (support c) [] (.collection (.objects x))) (hx : x ≠ 27) :
    (exactlyTwo e).Defined m ρ :=
  (e.cardinality_objects_defined m ρ hρ (hf x hx)).equal ⟨⟨2⟩,rfl⟩

-- [proof->req~clafer-appendix-f-expressions~1]
theorem c01_defined (m : IntegerBinding.{u,w} (support 1) U)
    (ρ : Environment (support 1) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c01.Defined m ρ :=
  ((some_defined m ρ hρ hf _ (by decide)).and
    (some_defined m ρ hρ hf _ (by decide))).implies
      (some_defined m ρ hρ hf _ (by decide))

theorem c03_defined (m : IntegerBinding.{u,w} (support 15) U)
    (ρ : Environment (support 15) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c03.Defined m ρ := no_defined m ρ hρ hf _ (by decide)

theorem c04_defined (m : IntegerBinding.{u,w} (support 15) U)
    (ρ : Environment (support 15) U []) (hρ : ρ.Admissible m) : c04.Defined m ρ := by
  obtain ⟨S,hS,_⟩ := (dereference12 (head12 (.widenObjects inclusion15 Expr.this))).collection_meaning m ρ hρ
  obtain ⟨T,hT,_⟩ := (Expr.widenObjects inclusion14 (parent15 Expr.this)).collection_meaning m ρ hρ
  exact Expr.Defined.equal ⟨S,hS⟩ ⟨T,hT⟩

theorem c05_defined (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c05.Defined m ρ :=
  (some_defined m ρ hρ hf _ (by decide)).iff (some_defined m ρ hρ hf _ (by decide))

theorem c06_defined (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c06.Defined m ρ :=
  (some_defined m ρ hρ hf _ (by decide)).iff (two_defined m ρ hρ hf _ (by decide))

theorem c07_defined (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c07.Defined m ρ :=
  (some_defined m ρ hρ hf _ (by decide)).iff
    ((some_defined m ρ hρ hf _ (by decide)).implies (two_defined m ρ hρ hf _ (by decide)))

theorem c08_defined (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c08.Defined m ρ :=
  (some_defined m ρ hρ hf _ (by decide)).iff (some_defined m ρ hρ hf _ (by decide)).not

theorem c09_defined (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c09.Defined m ρ :=
  (some_defined m ρ hρ hf _ (by decide)).iff (some_defined m ρ hρ hf _ (by decide)).not

theorem c10_defined (m : IntegerBinding.{u,w} (support 0) U)
    (ρ : Environment (support 0) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c10.Defined m ρ := some_defined m ρ hρ hf _ (by decide)

theorem c11_defined (m : IntegerBinding.{u,w} (support 0) U)
    (ρ : Environment (support 0) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c11.Defined m ρ := some_defined m ρ hρ hf _ (by decide)

theorem c12_defined (m : IntegerBinding.{u,w} (support 0) U)
    (ρ : Environment (support 0) U []) (hρ : ρ.Admissible m) (hf : FiniteStructural m) :
    c12.Defined m ρ := some_defined m ρ hρ hf _ (by decide)

/-- The six-class #67 support is a projection of the full resolved inventory;
its map carriers are the same original spans, not merely equal relations. -/
def versionGraph (m : IntegerBinding.{u,w} (support 11) U) :
    VersionNavigation.support.graph ⥤q semanticGraph.{u,w} U where
  obj x := m.model.obj ((![11,10,8,9,12,27] : Fin 6 → Fin 28) x)
  map := by
    rintro x y ⟨i,hs,ht⟩
    subst x; subst y
    exact (match i with
      | 0 => m.model.map ((support 11).arrow 27)
      | 1 => m.model.map ((support 11).arrow 26)
      | 2 => m.model.map ((support 11).arrow 6)
      | 3 => m.model.map ((support 11).arrow 23)
      | 4 => m.model.map ((support 11).arrow 7)
      | 5 => m.model.map ((support 11).arrow 24))

def versionModel (m : IntegerBinding.{u,w} (support 11) U)
    (vh : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 6)))
    (vd : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 23)))
    (sh : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 7)))
    (sd : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 24))) :
    VersionNavigation.Model.{u,w} U where
  realization := m.realization
  model := versionGraph m
  same_id := by
    intro x y h
    have he : x = y := by
      fin_cases x <;> fin_cases y <;> simp_all [VersionNavigation.support]
    subst y; rfl
  inclusion := by
    intro i hi
    fin_cases i
    · exact m.inclusion 27 rfl
    · exact m.inclusion 26 rfl
    all_goals cases hi
  integer_domain := by
    intro x hx
    fin_cases x <;> simp_all [VersionNavigation.support]
    exact m.integer_domain 27 rfl
  version_head := vh
  version_dref := vd
  server_head := sh
  server_dref := sd

theorem c02_defined (m : IntegerBinding.{u,w} (support 11) U)
    (vh : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 6)))
    (vd : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 23)))
    (sh : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 7)))
    (sd : TargetMultiplicity Clafer.one (m.model.map ((support 11).arrow 24)))
    (x : Subtype (m.model.obj (11 : Fin 28))) :
    c02.Defined m (.closed x.val) :=
  VersionNavigation.denotation_defined (versionModel m vh vd sh sd) x

-- [proof->req~clafer-constraint-semantic-laws~1]
/-- Absent ECU2 makes the implication in c07 true, even though zero displays
is not two. This is the actual c07 expansion, with no extra implication guard. -/
theorem c07_vacuity (m : IntegerBinding.{u,w} (support 19) U)
    (ρ : Environment (support 19) U []) (absent : (m.model.obj (17 : Fin 28) : Set U) = (∅ : Set U)) :
    c07.denote m ρ = (head23 Expr.this).some.denote m ρ := by
  have hp : (Expr.extent 17 : Expr (support 19) [] _).some.denote m ρ = some ⟨False⟩ := by
    have he : (Expr.extent 17 : Expr (support 19) [] _).denote m ρ = some (∅ : Set U) :=
      congrArg some absent
    simpa using denotes_some m ρ _ ∅ he Set.finite_empty
  have hc : (exactlyTwo displays2).denote m ρ = some ⟨False⟩ := by
    have hd : (displays2 : Expr (support 19) [] _).denote m ρ = some (∅ : Set U) := by
      change some (relationalImage (m.model.obj (17 : Fin 28)) _) = some ∅
      rw [absent]
      simp [relationalImage]
    simp [exactlyTwo,Expr.denote,hd,lift₂,finiteCard]
  have hi := denotes_implies m ρ _ _ False False hp hc
  apply denotes_iff_true
  simpa using hi

end Clafer.Examples.Telematics.Definedness
