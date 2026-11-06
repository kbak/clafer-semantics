module

public import FormalCD.Metamodel.InterpretationExamples

/-!
[impl->req~formalcd-metamodel-examples~1]
[proof->req~formalcd-formula-identity~1]
[proof->req~formalcd-metamodel-disciplines~1]
[proof->req~formalcd-metamodel-examples~1]
-/

/-! # Valid and invalid interpreted names (SoSyM §6.1.3 PDF pp.20–21)
A singleton carrier can be a realized predefined class or a user class. Both
cases are checked against actual name spans and the predefined inclusion square.
-/

@[expose] public section

namespace FormalCD.Metamodel.Examples
open CategoryTheory DPGraph DPGraph.Predicates

def functionSpan {A B : Type} (f : A → B) : Span A B := ⟨A, id, f⟩

def functionComp {A B C : Type} (f : A → B) (g : B → C) :
    Span.Iso ((functionSpan f).comp (functionSpan g)) (functionSpan (g ∘ f)) where
  equiv :=
    { toFun := fun l => l.val.1
      invFun := fun a => ⟨(a,f a), rfl⟩
      left_inv := fun l => Subtype.ext (Prod.ext rfl l.property)
      right_inv := fun _ => rfl }
  source_eq _ := rfl
  target_eq l := congrArg g l.property

def predefSet (b : Bool) : Set String := {c | c = "#C" ∧ b = true}
def emptySet : Set String := ∅

def predefToClass (b : Bool) (c : predefSet b) : one "#C" := ⟨c.val,c.property.1⟩
def toText (b : Bool) (_ : one "#C") : (Set.univ : Set String) :=
  ⟨if b then "SING" else "User", trivial⟩
def predefText (b : Bool) (_ : predefSet b) : one "SING" := point "SING"
def textIn (s : one "SING") : (Set.univ : Set String) := ⟨s.val,trivial⟩

def nameDiagram (b : Bool) : nameShape ⥤q semanticGraph String where
  obj | .class | .classifier => one "#C"
      | .predef | .sing => predefSet b
      | .dom | .map | .incl => emptySet
      | .string => Set.univ
      | .predefStr => one "SING"
  map | .classIn => functionSpan id
      | .mapIn => functionSpan (fun c => False.elim c.property)
      | .inclIn => functionSpan id
      | .predefIn => functionSpan (predefToClass b)
      | .singIn => functionSpan id
      | .domIn => functionSpan (fun c => False.elim c.property)
      | .predefStrIn => functionSpan textIn
      | .name => functionSpan (toText b)
      | .predefName => functionSpan (predefText b)

def nameContext (b : Bool) : NameContext registry String where
  text := Function.Embedding.refl _
  name _ := if b then "SING" else "User"
  identifier c := if c = "#C" ∧ b = true then some .sing else none

theorem name_square (b : Bool) : Nonempty (Span.Iso
    (((nameDiagram b).map NameEdge.predefIn).comp ((nameDiagram b).map NameEdge.classIn) |>.comp
      ((nameDiagram b).map NameEdge.name))
    (((nameDiagram b).map NameEdge.predefName).comp ((nameDiagram b).map NameEdge.predefStrIn))) := by
  have h : (toText b) ∘ (id ∘ predefToClass b) = textIn ∘ predefText b := by
    funext c
    apply Subtype.ext
    simp [toText, c.property.2, textIn, predefText, point]
  exact ⟨((functionComp (predefToClass b) id).comp (Span.Iso.refl (functionSpan (toText b)))).trans
    ((functionComp (id ∘ predefToClass b) (toText b)).trans
      (h ▸ (functionComp (predefText b) textIn).symm))⟩

theorem names_valid (b : Bool) : NameDiscipline (nameContext b) (nameDiagram b) where
  names _ := rfl
  predefined_names := by
    intro c hc i hi
    cases i
    cases b <;> simp_all [nameContext, registry]
  user_names := by
    intro c hc hi ⟨i,hn⟩
    cases i
    cases b <;> simp_all [objects, nameContext, nameDiagram, one, registry]
  unique_identifier := by
    intro c hc d hd _ _ _
    exact hc.trans hd.symm
  realized := by
    intro c
    cases b <;> simp [objects, nameDiagram, predefSet, nameContext, one, registry]
  reserved := by
    intro t; constructor
    · intro h; exact ⟨.sing, h.symm⟩
    · rintro ⟨i,h⟩; cases i; exact h.symm
  singleton_kind := by
    intro c
    cases b <;> simp [objects, nameDiagram, predefSet, nameContext, one, registry]
  primitive_kind := by
    intro c
    simp [objects, nameDiagram, emptySet, registry]
  inclusion_names := by intro c hc; exact hc.elim
  restriction := name_square b

theorem valid_user_name : (nameContext false).name "#C" = "User" ∧
    (nameContext false).identifier "#C" = none := ⟨rfl,rfl⟩

theorem valid_predefined_name : (nameContext true).name "#C" = registry.name MetaPredefined.sing ∧
    (nameContext true).identifier "#C" = some MetaPredefined.sing := ⟨rfl,rfl⟩

def reservedUser : NameContext registry String :=
  { nameContext false with name := fun _ => "SING" }

theorem reserved_user_rejected : ¬ NameDiscipline reservedUser (nameDiagram false) := by
  intro h
  exact h.user_names "#C" rfl rfl ⟨.sing,rfl⟩

def wrongPredefined : NameContext registry String :=
  { nameContext true with name := fun _ => "Wrong" }

theorem wrong_predefined_rejected : ¬ NameDiscipline wrongPredefined (nameDiagram true) := by
  intro h
  have he := h.predefined_names "#C" rfl .sing rfl
  exact (by decide : ("Wrong" : String) ≠ "SING") he

/-- Altering the interpreting name span also fails, even with valid registry data. -/
theorem incompatible_name_span_rejected : ¬ NameDiscipline (nameContext true) (nameDiagram false) := by
  intro h
  have he := h.names (point "#C")
  exact (by decide : ("User" : String) ≠ "SING") he

noncomputable def namedContext (b : Bool) : Context registry repeatSignature singleGraph String :=
  { repeatContext with names := nameContext b }

def fragmentNd : Formula vocabulary.signature nameShape := ⟨.inr .nd, Prefunctor.id _⟩

theorem extended_nd_satisfied (b : Bool) :
    (interpretation (namedContext b)).Satisfies (nameDiagram b) fragmentNd := names_valid b

end FormalCD.Metamodel.Examples
