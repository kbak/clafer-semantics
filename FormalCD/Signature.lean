module

public import DPGraph

/-!
# Supported signatures

SoSyM B.4 Definitions 7–8. A vocabulary contains the built-in predicates with
isomorphic arities, possibly in different universes. The isomorphisms are actual
Prefunctors with two inverse laws; no resizing or equality of universes is used.
-/

@[expose] public section

universe s va ua v u v' u' vm um

namespace FormalCD
open CategoryTheory

-- [impl->req~formalcd-signature-extension~1]
structure Vocabulary where
  signature : DPGraph.Signature.{s,va,ua}
  builtin : DPGraph.Predicates.Symbol ↪ signature.Symbol
  project : ∀ p, signature.arity (builtin p) ⥤q DPGraph.Predicates.signature.arity p
  lift : ∀ p, DPGraph.Predicates.signature.arity p ⥤q signature.arity (builtin p)
  lift_project : ∀ p, (lift p).comp (project p) = Prefunctor.id _
  project_lift : ∀ p, (project p).comp (lift p) = Prefunctor.id _

namespace Vocabulary

def builtins : Vocabulary where
  signature := DPGraph.Predicates.signature
  builtin := Function.Embedding.refl _
  project _ := Prefunctor.id _
  lift _ := Prefunctor.id _
  lift_project _ := rfl
  project_lift _ := rfl

/-- Disjoint extension with small arities. `Vocabulary` itself permits independent
arity universes; this constructor needs no lifts because both arities are small. -/
def extend (extra : DPGraph.Signature.{s,0,0}) : Vocabulary.{s,0,0} where
  signature := ⟨Sum DPGraph.Predicates.Symbol extra.Symbol,
    Sum.elim DPGraph.Predicates.signature.arity extra.arity⟩
  builtin := ⟨Sum.inl, Sum.inl_injective⟩
  project _ := Prefunctor.id _
  lift _ := Prefunctor.id _
  lift_project _ := rfl
  project_lift _ := rfl

variable (V : Vocabulary.{s,va,ua})

def embed {G : Quiv.{v,u}} (f : DPGraph.Formula DPGraph.Predicates.signature G) :
    DPGraph.Formula V.signature G := ⟨V.builtin f.symbol, (V.project f.symbol).comp f.binding⟩

@[simp] theorem embed_builtins {G : Quiv.{v,u}}
    (f : DPGraph.Formula DPGraph.Predicates.signature G) : builtins.embed f = f := by
  cases f; rfl

theorem embed_translate {G : Quiv.{v,u}} {H : Quiv.{v',u'}}
    (f : DPGraph.Formula DPGraph.Predicates.signature G) (F : G ⥤q H) :
    V.embed (f.translate F) = (V.embed f).translate F := rfl

theorem embed_injective {G : Quiv.{v,u}} : Function.Injective (V.embed (G := G)) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  have hs := V.builtin.injective (congrArg DPGraph.Formula.symbol h)
  cases hs
  have hb : (V.project p).comp b = (V.project p).comp c := by
    simpa only [embed, DPGraph.Formula.mk.injEq, heq_eq_eq, true_and] using h
  have hc := congrArg (fun d => (V.lift p).comp d) hb
  simpa only [← Prefunctor.comp_assoc, V.lift_project, Prefunctor.id_comp] using
    congrArg (DPGraph.Formula.mk p) hc

/-- Built-in meanings at any bounded or abstract semantic graph. -/
def restrict {Ω : Quiv.{vm,um}} (I : DPGraph.Interpretation V.signature Ω) :
    DPGraph.Interpretation DPGraph.Predicates.signature Ω where
  meaning p d := I.meaning (V.builtin p) ((V.project p).comp d)

@[simp] theorem satisfies_embed {G : Quiv.{v,u}} {Ω : Quiv.{vm,um}}
    (I : DPGraph.Interpretation V.signature Ω) (m : G ⥤q Ω)
    (f : DPGraph.Formula DPGraph.Predicates.signature G) :
    I.Satisfies m (V.embed f) ↔ (V.restrict I).Satisfies m f := Iff.rfl

/-- Add meanings without changing any existing predicate meaning. -/
def extendInterpretation {extra : DPGraph.Signature.{s,0,0}} {Ω : Quiv.{vm,um}}
    (I : DPGraph.Interpretation DPGraph.Predicates.signature Ω)
    (J : DPGraph.Interpretation extra Ω) :
    DPGraph.Interpretation (extend extra).signature Ω where
  meaning | .inl p => I.meaning p | .inr p => J.meaning p

-- [proof->req~formalcd-signature-extension~1]
theorem restrict_extend {extra : DPGraph.Signature.{s,0,0}} {Ω : Quiv.{vm,um}}
    (I : DPGraph.Interpretation DPGraph.Predicates.signature Ω)
    (J : DPGraph.Interpretation extra Ω) :
    (extend extra).restrict (extendInterpretation I J) = I := by
  cases I; rfl

end Vocabulary
end FormalCD
