module

public import DPGraph.Semantics

/-!
[impl->req~dpgraph-referent-image~1]
[proof->req~dpgraph-referent-image~1]
-/

/-! # Graphs of used referents

Derived from SoSyM Appendix 2 Definitions 6–10 and §6.2.5. A finite or infinite
inventory of arrow occurrences supplies endpoints in the existing Quiv API.
Equal referents identify occurrences only when incidence agrees. This construction
asserts neither a global pushout theorem nor any naming/default policy.
-/

@[expose] public section
namespace DPGraph.Gluing
open CategoryTheory
universe u v x y
variable {V : Type u} {E : Type v} {CV : Type x} {CE : Type y}

/-- The ordinary quiver of endpoint-indexed occurrences; no new graph API. -/
def origin (ends : E → V × V) : Quiv :=
  @Quiv.of V ⟨fun a b => {e : E // (ends e).1 = a ∧ (ends e).2 = b}⟩

def edge (ends : E → V × V) (e : E) :
    @Quiver.Hom (origin ends) _ (ends e).1 (ends e).2 := ⟨e, rfl, rfl⟩

abbrev Used {A : Type*} {B : Type*} (f : A → B) := {b // b ∈ Set.range f}
def identify {A : Type*} {B : Type*} (f : A → B) (a : A) : Used f := ⟨f a, ⟨a, rfl⟩⟩
noncomputable def representative {A : Type*} {B : Type*} (f : A → B) (b : Used f) : A :=
  b.property.choose

theorem representative_spec {A : Type*} {B : Type*} (f : A → B) (b : Used f) :
    f (representative f b) = b.val := b.property.choose_spec

@[simp] theorem identify_eq_iff {A : Type*} {B : Type*} (f : A → B) (a b : A) :
    identify f a = identify f b ↔ f a = f b := Subtype.ext_iff

variable (ends : E → V × V) (vertices : V → CV) (arrows : E → CE)

structure Incidence : Prop where
  source : ∀ e f, arrows e = arrows f → vertices (ends e).1 = vertices (ends f).1
  target : ∀ e f, arrows e = arrows f → vertices (ends e).2 = vertices (ends f).2

noncomputable def source (e : Used arrows) : Used vertices :=
  identify vertices (ends (representative arrows e)).1
noncomputable def target (e : Used arrows) : Used vertices :=
  identify vertices (ends (representative arrows e)).2

abbrev Arrow (a b : Used vertices) :=
  {e : Used arrows // source ends vertices arrows e = a ∧ target ends vertices arrows e = b}
noncomputable def graph : Quiv := @Quiv.of (Used vertices) ⟨Arrow ends vertices arrows⟩

variable {ends vertices arrows}
theorem source_identify (h : Incidence ends vertices arrows) (e : E) :
    source ends vertices arrows (identify arrows e) = identify vertices (ends e).1 :=
  Subtype.ext (h.source _ _ (representative_spec arrows (identify arrows e)))
theorem target_identify (h : Incidence ends vertices arrows) (e : E) :
    target ends vertices arrows (identify arrows e) = identify vertices (ends e).2 :=
  Subtype.ext (h.target _ _ (representative_spec arrows (identify arrows e)))
variable (ends vertices arrows)

noncomputable def label (h : Incidence ends vertices arrows) :
    origin ends ⥤q graph ends vertices arrows where
  obj := identify vertices
  map e := ⟨identify arrows e.val,
    (source_identify h e.val).trans (congrArg (identify vertices) e.property.1),
    (target_identify h e.val).trans (congrArg (identify vertices) e.property.2)⟩

theorem label_obj_surjective (h : Incidence ends vertices arrows) :
    Function.Surjective (label ends vertices arrows h).obj := by
  rintro ⟨v, w, rfl⟩
  exact ⟨w, rfl⟩

variable {σ : Signature} {ι : Sort*}
noncomputable def diagram (h : Incidence ends vertices arrows)
    (formulas : ι → Formula σ (origin ends)) : DPGraph σ :=
  ⟨graph ends vertices arrows,
    Set.range (fun i => (formulas i).translate (label ends vertices arrows h))⟩

noncomputable def labelHom (h : Incidence ends vertices arrows)
    (formulas : ι → Formula σ (origin ends)) :
    Hom ⟨origin ends, Set.range formulas⟩ (diagram ends vertices arrows h formulas) where
  toPrefunctor := label ends vertices arrows h
  preserves := by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩

end DPGraph.Gluing
