module

public import Clafer.Verification.Admission

-- [proof->req~clafer-finite-checker~1]

/-!
# Raw-table fidelity and entrypoint correctness

Accepted ordinary links are tuples; duplicates are rejected before decoding.
These proofs connect the public entrypoint, not merely its internal Boolean,
to the independent semantics. They do not claim native proof certificates.
-/

@[expose] public section
namespace Clafer.Verification
open Semantics
variable {n : Nat} (m : EffectiveCore n) (r : RawCandidate)

/-- Serialization validity, independent of semantic satisfaction. -/
structure TablesValid : Prop where
  objects : r.objects.Nodup
  root : r.root ∈ r.objects
  members : r.members.Nodup
  containment : r.containment.Nodup
  references : r.references.Nodup
  memberClass : ∀ row ∈ r.members, ∃ d, m.id d = row.1
  linkClass : ∀ row ∈ r.containment ++ r.references, ∃ d, m.id d = row.1
  memberObject : ∀ row ∈ r.members, row.2 ∈ r.objects
  linkObjects : ∀ row ∈ r.containment ++ r.references,
    row.2.1 ∈ r.objects ∧ row.2.2 ∈ r.objects

variable {r}

theorem decode_root (hr : r.root ∈ r.objects) :
    r.objects[(r.decode m hr).root] = r.root := by
  simp [RawCandidate.decode, List.getElem_idxOf]

theorem decode_members (hr : r.root ∈ r.objects) (d : Fin n) (x : Fin r.objects.length) :
    x ∈ (realize (r.decode m hr)).head d ↔ (m.id d, r.objects[x]) ∈ r.members := by
  change decide ((m.id d, r.objects[x]) ∈ r.members) = true ↔ _
  exact Iff.of_eq (decide_eq_true_eq (p := (m.id d, r.objects[x]) ∈ r.members))

theorem decode_containment (hr : r.root ∈ r.objects) (d : Fin n)
    (p x : Fin r.objects.length) :
    (realize (r.decode m hr)).contains d p x ↔
      (m.id d, r.objects[p], r.objects[x]) ∈ r.containment := by
  simp [realize, RawCandidate.decode]

theorem decode_references (hr : r.root ∈ r.objects) (d : Fin n)
    (x t : Fin r.objects.length) :
    (realize (r.decode m hr)).deref d x t ↔
      (m.id d, r.objects[x], r.objects[t]) ∈ r.references := by
  simp [realize, RawCandidate.decode]

/-- Arbitrary accepted object labels are bijective with canonical finite IDs. -/
def objectLabels (h : TablesValid m r) : Fin r.objects.length ≃ {x // x ∈ r.objects} where
  toFun i := ⟨r.objects[i], List.getElem_mem i.isLt⟩
  invFun x := ⟨r.objects.idxOf x.val, List.idxOf_lt_length_of_mem x.property⟩
  left_inv i := by
    apply Fin.ext
    exact (List.Nodup.getElem_inj_iff h.objects
      (hi := List.idxOf_lt_length_of_mem (List.getElem_mem i.isLt)) (hj := i.isLt)).mp (by simp)
  right_inv x := by apply Subtype.ext; simp

/-- No accepted membership row is lost in finite normalization. -/
theorem member_row_preserved (h : TablesValid m r) (row) (hr : row ∈ r.members) :
    ∃ d x, m.id d = row.1 ∧ r.objects[x] = row.2 ∧
      x ∈ (realize (r.decode m h.root)).head d := by
  obtain ⟨d, hd⟩ := h.memberClass row hr
  let x := (objectLabels m h).symm ⟨row.2, h.memberObject row hr⟩
  have hx : r.objects[x] = row.2 := congrArg Subtype.val ((objectLabels m h).apply_symm_apply _)
  exact ⟨d, x, hd, hx, (decode_members m h.root d x).mpr (by simpa [hd, hx] using hr)⟩

/-- Both ordinary map tables have complete endpoint and class inventories. -/
theorem link_row_indices (h : TablesValid m r) (row)
    (hr : row ∈ r.containment ++ r.references) :
    ∃ (d : Fin n) (x y : Fin r.objects.length), m.id d = row.1 ∧
      r.objects[x] = row.2.1 ∧ r.objects[y] = row.2.2 := by
  obtain ⟨d, hd⟩ := h.linkClass row hr
  obtain ⟨hx, hy⟩ := h.linkObjects row hr
  exact ⟨d, (objectLabels m h).symm ⟨row.2.1, hx⟩,
    (objectLabels m h).symm ⟨row.2.2, hy⟩, hd,
    congrArg Subtype.val ((objectLabels m h).apply_symm_apply _),
    congrArg Subtype.val ((objectLabels m h).apply_symm_apply _)⟩

/-- With unique resolved declaration IDs and unique object labels, normalization
cannot merge distinct ordinary tuple identities. -/
theorem tuple_identity (wf : m.WellFormed) (h : TablesValid m r)
    (d e : Fin n) (p x q y : Fin r.objects.length)
    (he : (m.id d, r.objects[p], r.objects[x]) = (m.id e, r.objects[q], r.objects[y])) :
    d = e ∧ p = q ∧ x = y := by
  have hc := wf.2.1 (congrArg Prod.fst he)
  have hp := (List.Nodup.getElem_inj_iff h.objects).mp (congrArg (fun z => z.2.1) he)
  have hx := (List.Nodup.getElem_inj_iff h.objects).mp (congrArg (fun z => z.2.2) he)
  exact ⟨hc, Fin.ext hp, Fin.ext hx⟩

theorem TablesValid.noUnknown (h : TablesValid m r) :
    ¬ ((∃ row ∈ r.members, ¬ ∃ d, m.id d = row.1) ∨
      (∃ row ∈ r.containment ++ r.references, ¬ ∃ d, m.id d = row.1)) := by
  rintro (⟨row, hr, hn⟩ | ⟨row, hr, hn⟩)
  · exact hn (h.memberClass row hr)
  · exact hn (h.linkClass row hr)

theorem TablesValid.noDangling (h : TablesValid m r) :
    ¬ ((∃ row ∈ r.members, row.2 ∉ r.objects) ∨
      (∃ row ∈ r.containment ++ r.references,
        row.2.1 ∉ r.objects ∨ row.2.2 ∉ r.objects)) := by
  rintro (⟨row, hr, hn⟩ | ⟨row, hr, hn⟩)
  · exact hn (h.memberObject row hr)
  · rcases hn with hn | hn
    · exact hn (h.linkObjects row hr).1
    · exact hn (h.linkObjects row hr).2

theorem verify_valid (h : TablesValid m r)
    (typed : (realize (r.decode m h.root)).Typed m) :
    verify m r = if check m (r.decode m h.root) then .satisfies else .violates := by
  unfold verify
  rw [ite_eq_right (not_not.mpr h.objects), dite_eq_right (not_not.mpr h.root),
    ite_eq_right (not_not.mpr h.members),
    ite_eq_right (by simp only [h.containment, h.references, not_true_eq_false, or_self, not_false_eq_true]),
    ite_eq_right (h.noUnknown m), ite_eq_right (h.noDangling m)]
  simp only [typed, not_true_eq_false, ite_false]

theorem verify_correct (wf : m.WellFormed) (support : m.Supported)
    (h : TablesValid m r) (typed : (realize (r.decode m h.root)).Typed m) :
    verify m r = .satisfies ↔ StructuralSatisfies m (realize (r.decode m h.root)) := by
  rw [verify_valid m h typed]
  simpa using check_correct m (r.decode m h.root) wf support

theorem verify_violation (wf : m.WellFormed) (support : m.Supported)
    (h : TablesValid m r) (typed : (realize (r.decode m h.root)).Typed m) :
    verify m r = .violates ↔ ¬ StructuralSatisfies m (realize (r.decode m h.root)) := by
  rw [verify_valid m h typed, ← check_correct m (r.decode m h.root) wf support]
  cases check m (r.decode m h.root) <;> simp

theorem illTyped_rejected (h : TablesValid m r)
    (typed : ¬ (realize (r.decode m h.root)).Typed m) :
    verify m r = .malformed .illTyped := by
  unfold verify
  rw [ite_eq_right (not_not.mpr h.objects), dite_eq_right (not_not.mpr h.root),
    ite_eq_right (not_not.mpr h.members),
    ite_eq_right (by simp only [h.containment, h.references, not_true_eq_false, or_self, not_false_eq_true]),
    ite_eq_right (h.noUnknown m), ite_eq_right (h.noDangling m)]
  simp only [typed, not_false_eq_true, ite_true]

/-- A successful protocol result entails every serialization validity check;
unknown rows or repeated identities cannot be silently normalized away. -/
theorem success_tablesValid (h : verify m r = .satisfies) : TablesValid m r := by
  classical
  unfold verify at h
  split_ifs at h with ho hr hm hl hc he
  refine ⟨ho, hr, hm,
    not_not.mp (fun hn => hl (Or.inl hn)), not_not.mp (fun hn => hl (Or.inr hn)),
    ?_, ?_, ?_, ?_⟩
  · intro row hrow
    by_contra hn
    exact hc (Or.inl ⟨row, hrow, hn⟩)
  · intro row hrow
    by_contra hn
    exact hc (Or.inr ⟨row, hrow, hn⟩)
  · intro row hrow
    by_contra hn
    exact he (Or.inl ⟨row, hrow, hn⟩)
  · intro row hrow
    constructor
    · by_contra hn
      exact he (Or.inr ⟨row, hrow, Or.inl hn⟩)
    · by_contra hn
      exact he (Or.inr ⟨row, hrow, Or.inr hn⟩)

theorem malformed_tables_rejected (h : ¬ TablesValid m r) : verify m r ≠ .satisfies :=
  fun hs => h (success_tablesValid m hs)

theorem run_correct (k : CoreCertificate n) (hc : coreChecks m k) (hs : supportChecks m k)
    (h : TablesValid m r) (typed : (realize (r.decode m h.root)).Typed m) :
    run m k r = .candidate .satisfies ↔ StructuralSatisfies m (realize (r.decode m h.root)) := by
  simp only [run, hc, hs, not_true_eq_false, ite_false, RunResult.candidate.injEq]
  exact verify_correct m (admitted_wellFormed m k hc hs) (admitted_supported m k hs) h typed

end Clafer.Verification
