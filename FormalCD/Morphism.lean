module

public import FormalCD.Basic

/-!
[impl->req~formalcd-morphisms~1]
[impl->req~formalcd-signature-extension~1]
[proof->req~formalcd-morphisms~1]
[proof->req~formalcd-signature-extension~1]
-/

/-!
# Name-preserving FormalCD morphisms

An adopted library specialization of SoSyM B.4 Definition 10. The additional
metadata equalities are not attributed to the paper's generic DP morphisms.
Source and target are independently well-formed, at one shared registry.
-/

@[expose] public section

universe s va ua p v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace FormalCD

variable {Vocab : Vocabulary.{s,va,ua}} {R : Registry.{p}}

/-- Declaration preservation plus equality of all metadata at mapped identities.
No carrier injectivity or reflection of extra target declarations is required. -/
structure HomOver (S : CDOver.{s,va,ua,p,v₁,u₁} Vocab R) (T : CDOver.{s,va,ua,p,v₂,u₂} Vocab R) where
  toDPHom : DPGraph.Hom S.toDPGraph T.toDPGraph
  className_eq : ∀ c, T.className (toDPHom.toPrefunctor.obj c) = S.className c
  mapName_eq : ∀ {a b} (e : a ⟶ b),
    T.mapName (toDPHom.toPrefunctor.map e) = S.mapName e
  predefined_eq : ∀ c, T.predefined (toDPHom.toPrefunctor.obj c) = S.predefined c
  mode_eq : ∀ {a b} (e : a ⟶ b), T.mode (toDPHom.toPrefunctor.map e) = S.mode e

namespace HomOver

variable {S : CDOver.{s,va,ua,p,v₁,u₁} Vocab R} {T : CDOver.{s,va,ua,p,v₂,u₂} Vocab R}
variable {U : CDOver.{s,va,ua,p,v₃,u₃} Vocab R} {V : CDOver.{s,va,ua,p,v₄,u₄} Vocab R}

@[ext] theorem ext {F J : HomOver S T} (h : F.toDPHom = J.toDPHom) : F = J := by
  cases F; cases J; cases h; rfl

theorem ext_of_map {F J : HomOver S T}
    (h : F.toDPHom.toPrefunctor = J.toDPHom.toPrefunctor) : F = J :=
  ext (DPGraph.Hom.ext h)

def id (S : CDOver.{s,va,ua,p,v₁,u₁} Vocab R) : HomOver S S where
  toDPHom := DPGraph.Hom.id S.toDPGraph
  className_eq _ := rfl
  mapName_eq _ := rfl
  predefined_eq _ := rfl
  mode_eq _ := rfl

def comp (F : HomOver S T) (J : HomOver T U) : HomOver S U where
  toDPHom := F.toDPHom.comp J.toDPHom
  className_eq c := (J.className_eq _).trans (F.className_eq c)
  mapName_eq e := (J.mapName_eq _).trans (F.mapName_eq e)
  predefined_eq c := (J.predefined_eq _).trans (F.predefined_eq c)
  mode_eq e := (J.mode_eq _).trans (F.mode_eq e)

@[simp] theorem toDPHom_id (S : CDOver.{s,va,ua,p,v₁,u₁} Vocab R) :
    (id S).toDPHom = DPGraph.Hom.id S.toDPGraph := rfl

@[simp] theorem toDPHom_comp (F : HomOver S T) (J : HomOver T U) :
    (F.comp J).toDPHom = F.toDPHom.comp J.toDPHom := rfl

@[simp] theorem id_comp (F : HomOver S T) : (id S).comp F = F :=
  ext (DPGraph.Hom.id_comp F.toDPHom)

@[simp] theorem comp_id (F : HomOver S T) : F.comp (id T) = F :=
  ext (DPGraph.Hom.comp_id F.toDPHom)

theorem comp_assoc (F : HomOver S T) (J : HomOver T U) (K : HomOver U V) :
    (F.comp J).comp K = F.comp (J.comp K) :=
  ext (DPGraph.Hom.comp_assoc F.toDPHom J.toDPHom K.toDPHom)

end HomOver
/-- Declaration preservation plus equality of all metadata at mapped identities.
No carrier injectivity or reflection of extra target declarations is required. -/
abbrev Hom (S : CD.{p,v₁,u₁} R) (T : CD.{p,v₂,u₂} R) :=
  HomOver S.generalize T.generalize

namespace Hom

variable {S : CD.{p,v₁,u₁} R} {T : CD.{p,v₂,u₂} R}
variable {U : CD.{p,v₃,u₃} R} {V : CD.{p,v₄,u₄} R}

/-- Original projection names specialize the common implementation. -/
abbrev toDPHom (F : Hom S T) : DPGraph.Hom S.toDPGraph T.toDPGraph := HomOver.toDPHom F
abbrev className_eq (F : Hom S T) : ∀ c,
    T.className (F.toDPHom.toPrefunctor.obj c) = S.className c := HomOver.className_eq F
abbrev mapName_eq (F : Hom S T) : ∀ {a b} (e : a ⟶ b),
    T.mapName (F.toDPHom.toPrefunctor.map e) = S.mapName e := HomOver.mapName_eq F
abbrev predefined_eq (F : Hom S T) : ∀ c,
    T.predefined (F.toDPHom.toPrefunctor.obj c) = S.predefined c := HomOver.predefined_eq F
abbrev mode_eq (F : Hom S T) : ∀ {a b} (e : a ⟶ b),
    T.mode (F.toDPHom.toPrefunctor.map e) = S.mode e := HomOver.mode_eq F

@[ext] theorem ext {F J : Hom S T} (h : F.toDPHom = J.toDPHom) : F = J := by
  cases F; cases J; cases h; rfl

theorem ext_of_map {F J : Hom S T}
    (h : F.toDPHom.toPrefunctor = J.toDPHom.toPrefunctor) : F = J :=
  ext (DPGraph.Hom.ext h)

def id (S : CD.{p,v₁,u₁} R) : Hom S S where
  toDPHom := DPGraph.Hom.id S.toDPGraph
  className_eq _ := rfl
  mapName_eq _ := rfl
  predefined_eq _ := rfl
  mode_eq _ := rfl

def comp (F : Hom S T) (J : Hom T U) : Hom S U where
  toDPHom := F.toDPHom.comp J.toDPHom
  className_eq c := (J.className_eq _).trans (F.className_eq c)
  mapName_eq e := (J.mapName_eq _).trans (F.mapName_eq e)
  predefined_eq c := (J.predefined_eq _).trans (F.predefined_eq c)
  mode_eq e := (J.mode_eq _).trans (F.mode_eq e)

@[simp] theorem toDPHom_id (S : CD.{p,v₁,u₁} R) :
    (id S).toDPHom = DPGraph.Hom.id S.toDPGraph := rfl

@[simp] theorem toDPHom_comp (F : Hom S T) (J : Hom T U) :
    (F.comp J).toDPHom = F.toDPHom.comp J.toDPHom := rfl

@[simp] theorem id_comp (F : Hom S T) : (id S).comp F = F :=
  ext (DPGraph.Hom.id_comp F.toDPHom)

@[simp] theorem comp_id (F : Hom S T) : F.comp (id T) = F :=
  ext (DPGraph.Hom.comp_id F.toDPHom)

theorem comp_assoc (F : Hom S T) (J : Hom T U) (K : Hom U V) :
    (F.comp J).comp K = F.comp (J.comp K) :=
  ext (DPGraph.Hom.comp_assoc F.toDPHom J.toDPHom K.toDPHom)

end Hom
end FormalCD
