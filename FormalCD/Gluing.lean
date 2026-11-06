module

public import DPGraph.Gluing
public import FormalCD.Morphism

/-!
[impl->req~formalcd-referent-descent~1]
[proof->req~formalcd-referent-descent~1]
-/

/-! # Metadata and effective defaults on a referent graph

SoSyM §6.1.1–3 and §6.2.5, using Appendix 2 Definition 10. Metadata must be
constant on the identification fibers. Names do not generate those fibers;
complete effective defaults remain hypotheses, never inserted declarations.
-/

@[expose] public section
namespace FormalCD.Gluing
open CategoryTheory DPGraph.Gluing

variable {V E CV CE : Type} {R : Registry.{0}}

/-- Metadata on an occurrence inventory, independently of referent selection. -/
structure Metadata (V E : Type) (R : Registry.{0}) where
  className : V → String
  mapName : E → String
  predefined : V → Option R.Id
  mode : E → MapMode

variable (ends : E → V × V) (vertices : V → CV) (arrows : E → CE)
variable (metadata : Metadata V E R)

/-- Invalid inputs have no proof of this proposition; conflicts are never repaired.
Registry kinds follow registry identity, so equal annotations also preserve kinds. -/
structure Compatible : Prop extends Incidence ends vertices arrows where
  class_name : ∀ v w, vertices v = vertices w → metadata.className v = metadata.className w
  map_name : ∀ m n, arrows m = arrows n → metadata.mapName m = metadata.mapName n
  predefined : ∀ v w, vertices v = vertices w → metadata.predefined v = metadata.predefined w
  mode : ∀ m n, arrows m = arrows n → metadata.mode m = metadata.mode n

variable {W : FormalCD.Vocabulary.{0,0,0}} {ι : Sort*}

noncomputable def raw (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends)) :
    FormalCD.RawOver W R where
  toDPGraph := diagram ends vertices arrows h.toIncidence d
  className v := metadata.className (representative vertices v)
  mapName e := metadata.mapName (representative arrows e.val)
  predefined v := metadata.predefined (representative vertices v)
  mode e := metadata.mode (representative arrows e.val)

variable {ends vertices arrows metadata}

@[simp] theorem className_label (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    (v : V) :
    (raw ends vertices arrows metadata h d).className (identify vertices v) = metadata.className v :=
  h.class_name _ _ (representative_spec vertices (identify vertices v))

@[simp] theorem mapName_label (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    {a b : origin ends} (e : a ⟶ b) :
    (raw ends vertices arrows metadata h d).mapName ((label ends vertices arrows h.toIncidence).map e) =
      metadata.mapName e.val :=
  h.map_name _ _ (representative_spec arrows (identify arrows e.val))

@[simp] theorem predefined_label (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    (v : V) :
    (raw ends vertices arrows metadata h d).predefined (identify vertices v) = metadata.predefined v :=
  h.predefined _ _ (representative_spec vertices (identify vertices v))

theorem kind_label (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    (v : V) :
    ((raw ends vertices arrows metadata h d).predefined (identify vertices v)).map R.kind =
      (metadata.predefined v).map R.kind := by
  rw [predefined_label]

@[simp] theorem mode_label (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    {a b : origin ends} (e : a ⟶ b) :
    (raw ends vertices arrows metadata h d).mode ((label ends vertices arrows h.toIncidence).map e) =
      metadata.mode e.val :=
  h.mode _ _ (representative_spec arrows (identify arrows e.val))

variable (ends vertices arrows metadata)

/-- Naming assumptions on the input, independently of declaration preservation.
Predefined uniqueness is required at referent identity, not at role identity. -/
structure Naming : Prop where
  predefined_name : ∀ v i, metadata.predefined v = some i → metadata.className v = R.name i
  user_name : ∀ v, metadata.predefined v = none → ¬R.Reserved (metadata.className v)
  unique_predefined : ∀ v w i, metadata.predefined v = some i → metadata.predefined w = some i →
    vertices v = vertices w
  inclusion_name : ∀ m, metadata.mode m = .inclusion → metadata.mapName m = "isA"

/-- Effective defaults must already be in the source bank. Bag maps have no
obligation here. Incidence and compatible metadata alone do not imply this property. -/
structure Defaults (d : ι → DPGraph.Formula W.signature (origin ends)) : Prop where
  inclusion : ∀ m, metadata.mode m = .inclusion →
    W.embed (FormalCD.inclusionFormula (G := origin ends) (edge ends m)) ∈ Set.range d
  ordinary : ∀ m, metadata.mode m = .ordinary →
    W.embed (FormalCD.setValuedFormula (G := origin ends) (edge ends m)) ∈ Set.range d

variable {ends vertices arrows metadata}

theorem raw_wellFormed (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    (hn : Naming vertices metadata) (hd : Defaults ends metadata d) :
    (raw ends vertices arrows metadata h d).WellFormed where
  predefined_name v i hi := hn.predefined_name _ i hi
  user_name v hv := hn.user_name _ hv
  unique_predefined v w i hv hw := by
    apply Subtype.ext
    have he := hn.unique_predefined _ _ i hv hw
    exact (representative_spec vertices v).symm.trans (he.trans (representative_spec vertices w))
  inclusion_name e he := hn.inclusion_name _ he
  inclusion_decl := by
    intro a b e he
    rcases e with ⟨m, rfl, rfl⟩
    have hp := (labelHom ends vertices arrows h.toIncidence d).preserves
      (hd.inclusion (representative arrows m) he)
    have hf := (W.embed_translate
      (FormalCD.inclusionFormula (G := origin ends) (edge ends (representative arrows m)))
      (label ends vertices arrows h.toIncidence)).symm.trans
      (congrArg W.embed (FormalCD.inclusionFormula_translate
        (G := origin ends) (edge ends (representative arrows m))
        (label ends vertices arrows h.toIncidence)))
    have hp' := hf ▸ hp
    have hm : (label ends vertices arrows h.toIncidence).map (edge ends (representative arrows m)) =
        (⟨m, rfl, rfl⟩ : Arrow ends vertices arrows
          (source ends vertices arrows m) (target ends vertices arrows m)) :=
      Subtype.ext (Subtype.ext (representative_spec arrows m))
    exact (congrArg (fun e => W.embed (FormalCD.inclusionFormula e) ∈
      (diagram ends vertices arrows h.toIncidence d).declarations) hm).mp hp'
  ordinary_decl := by
    intro a b e he
    rcases e with ⟨m, rfl, rfl⟩
    have hp := (labelHom ends vertices arrows h.toIncidence d).preserves
      (hd.ordinary (representative arrows m) he)
    have hf := (W.embed_translate
      (FormalCD.setValuedFormula (G := origin ends) (edge ends (representative arrows m)))
      (label ends vertices arrows h.toIncidence)).symm.trans
      (congrArg W.embed (FormalCD.setValuedFormula_translate
        (G := origin ends) (edge ends (representative arrows m))
        (label ends vertices arrows h.toIncidence)))
    have hp' := hf ▸ hp
    have hm : (label ends vertices arrows h.toIncidence).map (edge ends (representative arrows m)) =
        (⟨m, rfl, rfl⟩ : Arrow ends vertices arrows
          (source ends vertices arrows m) (target ends vertices arrows m)) :=
      Subtype.ext (Subtype.ext (representative_spec arrows m))
    exact (congrArg (fun e => W.embed (FormalCD.setValuedFormula e) ∈
      (diagram ends vertices arrows h.toIncidence d).declarations) hm).mp hp'

noncomputable def cd (h : Compatible ends vertices arrows metadata)
    (d : ι → DPGraph.Formula W.signature (origin ends))
    (hn : Naming vertices metadata) (hd : Defaults ends metadata d) : FormalCD.CDOver W R :=
  ⟨raw ends vertices arrows metadata h d, raw_wellFormed h d hn hd⟩

end FormalCD.Gluing
