module

public import FormalCD.Telematics.VC

/-!
[impl->req~formalcd-vc-witnesses~1]
[proof->req~formalcd-vc-witnesses~1]
-/

/-!
# Nonempty models and the four VC boundary witnesses

SoSyM Figure 21a–b, §6.1.1–3, corrected Q7. Only these example component/link
sets are finite. The integer class realizes every Int in the ambient Bool ⊕ Int.
Changing versions or removing server links preserves all eleven other formulas.
All assertions use the actual extended interpretation and typed declarations.
-/

@[expose] public section

namespace FormalCD.Telematics.Examples
open CategoryTheory DPGraph.Predicates

abbrev Universe := Sum Bool Int

def integers : IntegerRealization Universe where
  encode := ⟨Sum.inr, Sum.inr_injective⟩
  decode | .inl _ => 0 | .inr n => n
  decode_encode _ := rfl

def components : Set Universe := Set.range Sum.inl
def singletonObjects (b : Bool) : Set Universe := {x | x = Sum.inl b}
def component (b : Bool) : components := ⟨.inl b, ⟨b,rfl⟩⟩
def singletonObject (b : Bool) : singletonObjects b := ⟨.inl b,rfl⟩

instance (b : Bool) : Subsingleton (singletonObjects b) :=
  ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩

def inclusionSpan (b : Bool) : DPGraph.Span (singletonObjects b) components where
  Link := singletonObjects b
  source := id
  target x := ⟨x.val, ⟨b,x.property.symm⟩⟩

theorem inclusion_holds (b : Bool) : Inclusion (inclusionSpan b) :=
  ⟨Function.bijective_id, fun _ => rfl⟩

def serverSpan (served : Bool) : DPGraph.Span (singletonObjects true) (singletonObjects false) where
  Link := {_x : Unit // served = true}
  source _ := singletonObject true
  target _ := singletonObject false

/-- Both component versions are arbitrary integers, including negative values. -/
def versionNumber (ecuVersion displayVersion : Int) (c : components) : Int :=
  if c.val = Sum.inl true then displayVersion else ecuVersion

def versionSpan (ecuVersion displayVersion : Int) : DPGraph.Span components integers.domain where
  Link := components
  source := id
  target c := ⟨Sum.inr (versionNumber ecuVersion displayVersion c), ⟨_,rfl⟩⟩

def objects : Node → Set Universe
  | .comp => components
  | .ecu => singletonObjects false
  | .display => singletonObjects true
  | .int => integers.domain

def modelMap (served : Bool) (ecuVersion displayVersion : Int) :
    graph ⥤q semanticGraph.{0,0} Universe where
  obj := objects
  map
    | .i1 => inclusionSpan false
    | .i2 => inclusionSpan true
    | .server => serverSpan served
    | .display => (serverSpan served).inverse
    | .version => versionSpan ecuVersion displayVersion

/-- Empty or singleton fibers fit a zero lower bound; no totality is inferred. -/
theorem zero_upper {F : Type} [Subsingleton F] {n : Nat} (hn : 0 < n) :
    InRange ⟨0, .finite n⟩ F :=
  ⟨⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩⟩,
    ⟨⟨fun _ => ⟨0,hn⟩, fun _ _ _ => Subsingleton.elim _ _⟩⟩⟩

theorem server_multiplicity (served : Bool) :
    TargetMultiplicity ⟨0, .finite 1⟩ (serverSpan served) := by
  intro a
  have : Subsingleton ((serverSpan served).Link) :=
    inferInstanceAs (Subsingleton {_x : Unit // served = true})
  have : Subsingleton ((serverSpan served).toFamily.Index a) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact zero_upper (by decide)

theorem display_multiplicity (served : Bool) :
    TargetMultiplicity ⟨0, .finite 5⟩ (serverSpan served).inverse := by
  intro a
  have : Subsingleton ((serverSpan served).inverse.Link) :=
    inferInstanceAs (Subsingleton {_x : Unit // served = true})
  have : Subsingleton ((serverSpan served).inverse.toFamily.Index a) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact zero_upper (by decide)

theorem version_multiplicity (e d : Int) :
    TargetMultiplicity ⟨1, .finite 1⟩ (versionSpan e d) := by
  intro c
  refine ⟨⟨⟨fun _ => ⟨c,rfl⟩, fun _ _ _ => Subsingleton.elim _ _⟩⟩, ⟨⟨fun _ => 0, ?_⟩⟩⟩
  intro x y _
  exact Subtype.ext (x.property.trans y.property.symm)

theorem server_set (served : Bool) : SetValued (serverSpan served) :=
  fun _ _ _ => Subtype.ext (Subsingleton.elim _ _)
theorem display_set (served : Bool) : SetValued (serverSpan served).inverse :=
  (setValued_inverse _).mpr (server_set served)
theorem version_set (e d : Int) : SetValued (versionSpan e d) :=
  fun _ _ h => congrArg Prod.fst h

theorem inverse_holds (served : Bool) : Inverse (serverSpan served) (serverSpan served).inverse :=
  ⟨DPGraph.Span.Iso.refl _⟩

theorem cover_holds (s : Bool) (e d : Int) :
    (interpretation integers).Satisfies (modelMap s e d) (declaration .cover) := by
  rintro ⟨x,b,rfl⟩
  cases b
  · exact ⟨0, singletonObject false, rfl⟩
  · exact ⟨1, singletonObject true, rfl⟩

theorem disjoint_holds (s : Bool) (e d : Int) :
    (interpretation integers).Satisfies (modelMap s e d) (declaration .disjoint) := by
  intro i j hij l k he
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · have hv := congrArg Subtype.val he
    change l.val = k.val at hv
    have bad := l.property.symm.trans (hv.trans k.property)
    cases bad
  · have hv := congrArg Subtype.val he
    change l.val = k.val at hv
    have bad := l.property.symm.trans (hv.trans k.property)
    cases bad
  · exact hij rfl

/-- Every effective declaration other than VC holds for arbitrary integer versions. -/
theorem other_declarations (s : Bool) (e d : Int) (c : Declaration) (hc : c ≠ .vc) :
    (interpretation integers).Satisfies (modelMap s e d) (declaration c) := by
  cases c
  · exact disjoint_holds s e d
  · exact cover_holds s e d
  · exact inverse_holds s
  · exact inclusion_holds false
  · exact inclusion_holds true
  · exact display_multiplicity s
  · exact version_multiplicity e d
  · exact server_multiplicity s
  · exact (hc rfl).elim
  · exact version_set e d
  · exact server_set s
  · exact display_set s

/-- Computation of inherited versions still follows actual inclusion/version links. -/
theorem inherited_version (b : Bool) (e d n : Int) :
    InheritedVersion integers (inclusionSpan b) (versionSpan e d) (singletonObject b) n ↔
      n = if b then d else e := by
  constructor
  · rintro ⟨i,v,hi,hv,hn⟩
    have hiv : i.val = Sum.inl b := i.property
    have hvv : v.val = Sum.inl b := (congrArg Subtype.val hv).trans hiv
    change versionNumber e d v = n at hn
    rw [← hn]
    cases b <;> simp [versionNumber, hvv]
  · intro hn
    refine ⟨singletonObject b, component b, rfl, rfl, ?_⟩
    change versionNumber e d (component b) = n
    rw [hn]
    cases b <;> simp [versionNumber, component]

theorem vc_iff (s : Bool) (e d : Int) :
    (interpretation integers).Satisfies (modelMap s e d) vc ↔ (s = true → e ≤ d) := by
  change (objects .int = integers.domain ∧ _) ↔ _
  constructor
  · intro h hs
    exact h.2 ⟨(),hs⟩ d e
      ((inherited_version true e d d).mpr rfl)
      ((inherited_version false e d e).mpr rfl)
  · intro h
    refine ⟨rfl, ?_⟩
    intro sl nd ne hd he
    have hd' : nd = d := (inherited_version true e d nd).mp hd
    have he' : ne = e := (inherited_version false e d ne).mp he
    rw [hd',he']
    exact h sl.property

theorem model_iff (s : Bool) (e d : Int) :
    (interpretation integers).IsModel diagram.toDPGraph (modelMap s e d) ↔
      (s = true → e ≤ d) := by
  constructor
  · intro h
    exact (vc_iff s e d).mp (h _ (declared .vc))
  · intro h f ⟨c,hc⟩
    subst f
    by_cases hv : c = .vc
    · subst c; exact (vc_iff s e d).mpr h
    · exact other_declarations s e d c hv

/-- A nonempty whole model, including all twelve effective declarations. -/
def model : (interpretation integers).Model diagram.toDPGraph :=
  ⟨modelMap true 2 3, (model_iff true 2 3).mpr (by intro _; decide)⟩

theorem component_classes_nonempty : Nonempty components ∧
    Nonempty (singletonObjects false) ∧ Nonempty (singletonObjects true) :=
  ⟨⟨component false⟩, ⟨singletonObject false⟩, ⟨singletonObject true⟩⟩
theorem every_integer_realized (n : Int) : integers.encode n ∈ objects .int :=
  ⟨n,rfl⟩

theorem served_link : (serverSpan true).red (singletonObject true) (singletonObject false) :=
  ⟨⟨(),rfl⟩,rfl,rfl⟩

theorem greater_vc : (interpretation integers).Satisfies (modelMap true 2 3) vc :=
  (vc_iff true 2 3).mpr (by intro _; decide)
theorem equal_vc : (interpretation integers).Satisfies (modelMap true 2 2) vc :=
  (vc_iff true 2 2).mpr (by intro _; decide)
theorem lower_not_vc : ¬ (interpretation integers).Satisfies (modelMap true 3 2) vc := by
  intro h; have bad := (vc_iff true 3 2).mp h rfl; exact (by decide : ¬ (3 : Int) ≤ 2) bad

theorem lower_other_declarations (c : Declaration) (hc : c ≠ .vc) :
    (interpretation integers).Satisfies (modelMap true 3 2) (declaration c) :=
  other_declarations true 3 2 c hc

theorem unserved_vc : (interpretation integers).Satisfies (modelMap false 3 2) vc :=
  (vc_iff false 3 2).mpr (by intro h; cases h)
theorem unserved_model :
    (interpretation integers).IsModel diagram.toDPGraph (modelMap false 3 2) :=
  (model_iff false 3 2).mpr (by intro h; cases h)
theorem unserved_no_link : ¬ ∃ e, (serverSpan false).red (singletonObject true) e := by
  rintro ⟨e,l,_,_⟩; cases l.property

theorem unserved_multiplicity :
    (interpretation integers).Satisfies (modelMap false 3 2) (declaration .serverMult) :=
  server_multiplicity false

theorem unserved_not_total : ¬ Total (serverSpan false) := by
  intro h
  obtain ⟨l,_⟩ := h (singletonObject true)
  cases l.property

end FormalCD.Telematics.Examples
