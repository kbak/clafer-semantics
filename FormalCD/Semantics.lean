module

public import FormalCD.Morphism

/-!
[impl->req~formalcd-morphisms~1]
[impl->req~formalcd-signature-extension~1]
[proof->req~formalcd-morphisms~1]
[proof->req~formalcd-signature-extension~1]
-/

/-!
# Reusing the DPGraph reduct

SoSyM B.5's contravariant restriction applies after forgetting metadata.
The explicit interpretation concerns declared predicates; the registry does not
enforce Int/String/Bool/singleton domains on the interpreting graph map.
-/

@[expose] public section

universe s va ua p v₁ u₁ v₂ u₂ v₃ u₃ vm um

namespace FormalCD.HomOver

open CategoryTheory DPGraph.Predicates

variable {Vocab : Vocabulary.{s,va,ua}} {R : Registry.{p}} {Ω : Quiv.{vm,um}}
variable (I : DPGraph.Interpretation Vocab.signature Ω)
variable {S : CDOver.{s,va,ua,p,v₁,u₁} Vocab R} {T : CDOver.{s,va,ua,p,v₂,u₂} Vocab R} {U : CDOver.{s,va,ua,p,v₃,u₃} Vocab R}

def reduct (F : HomOver S T) (m : I.Model T.toDPGraph) : I.Model S.toDPGraph :=
  I.reduct F.toDPHom m

@[simp] theorem reduct_val (F : HomOver S T) (m : I.Model T.toDPGraph) :
    (reduct I F m).val = F.toDPHom.toPrefunctor.comp m.val := rfl

@[simp] theorem reduct_id (m : I.Model S.toDPGraph) : reduct I (id S) m = m :=
  I.reduct_id m

theorem reduct_comp (F : HomOver S T) (J : HomOver T U) (m : I.Model U.toDPGraph) :
    reduct I (F.comp J) m = reduct I F (reduct I J m) :=
  I.reduct_comp F.toDPHom J.toDPHom m

end FormalCD.HomOver

namespace FormalCD.Hom

open CategoryTheory DPGraph.Predicates

variable {R : Registry.{p}} {Ω : Quiv.{vm,um}}
variable (I : DPGraph.Interpretation signature Ω)
variable {S : CD.{p,v₁,u₁} R} {T : CD.{p,v₂,u₂} R} {U : CD.{p,v₃,u₃} R}

def reduct (F : Hom S T) (m : I.Model T.toDPGraph) : I.Model S.toDPGraph :=
  I.reduct F.toDPHom m

@[simp] theorem reduct_val (F : Hom S T) (m : I.Model T.toDPGraph) :
    (reduct I F m).val = F.toDPHom.toPrefunctor.comp m.val := rfl

@[simp] theorem reduct_id (m : I.Model S.toDPGraph) : reduct I (id S) m = m :=
  I.reduct_id m

theorem reduct_comp (F : Hom S T) (J : Hom T U) (m : I.Model U.toDPGraph) :
    reduct I (F.comp J) m = reduct I F (reduct I J m) :=
  I.reduct_comp F.toDPHom J.toDPHom m

end FormalCD.Hom
