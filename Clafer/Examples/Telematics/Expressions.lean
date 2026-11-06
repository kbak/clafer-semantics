module

public import Clafer.Examples.Telematics.Structural
public import Clafer.Constraints.DenotationLaws

/-!
# Manual resolved telematics expressions

SoSyM Appendix 6 PDF p.34 and D.1–D.4, accepted Q3/Q7. Source IDs and
contexts are exactly c01–c12 in docs/inherited-realization.md. This extends
that structural projection with separately typed bodies, without asserting
Compile/gluing preservation or correctness of a textual resolver.
-/

@[expose] public section
namespace Clafer.Examples.Telematics.Expressions
open Clafer.Constraints CategoryTheory

def maps : Fin 34 → MapRef 28 := ![⟨⟨2⟩, .head, 1, 2, "head"⟩,
  ⟨⟨3⟩, .head, 2, 3, "head"⟩,
  ⟨⟨4⟩, .head, 2, 4, "head"⟩,
  ⟨⟨5⟩, .head, 1, 5, "head"⟩,
  ⟨⟨6⟩, .head, 5, 6, "head"⟩,
  ⟨⟨7⟩, .head, 6, 7, "head"⟩,
  ⟨⟨9⟩, .head, 8, 9, "head"⟩,
  ⟨⟨12⟩, .head, 11, 12, "head"⟩,
  ⟨⟨13⟩, .head, 11, 13, "head"⟩,
  ⟨⟨15⟩, .head, 14, 15, "head"⟩,
  ⟨⟨16⟩, .head, 0, 16, "head"⟩,
  ⟨⟨17⟩, .head, 0, 17, "head"⟩,
  ⟨⟨18⟩, .head, 17, 18, "head"⟩,
  ⟨⟨19⟩, .head, 0, 19, "head"⟩,
  ⟨⟨20⟩, .head, 19, 20, "head"⟩,
  ⟨⟨21⟩, .head, 20, 21, "head"⟩,
  ⟨⟨22⟩, .head, 20, 22, "head"⟩,
  ⟨⟨23⟩, .head, 19, 23, "head"⟩,
  ⟨⟨24⟩, .head, 19, 24, "head"⟩,
  ⟨⟨25⟩, .head, 24, 25, "head"⟩,
  ⟨⟨26⟩, .head, 24, 26, "head"⟩,
  ⟨⟨27⟩, .head, 0, 27, "head"⟩,
  ⟨⟨6⟩, .dereference, 6, 27, "dereference"⟩,
  ⟨⟨9⟩, .dereference, 9, 27, "dereference"⟩,
  ⟨⟨12⟩, .dereference, 12, 10, "dereference"⟩,
  ⟨⟨18⟩, .dereference, 18, 16, "dereference"⟩,
  ⟨⟨10⟩, .inclusion, 10, 8, "inclusion"⟩,
  ⟨⟨11⟩, .inclusion, 11, 8, "inclusion"⟩,
  ⟨⟨13⟩, .inclusion, 13, 1, "inclusion"⟩,
  ⟨⟨14⟩, .inclusion, 14, 10, "inclusion"⟩,
  ⟨⟨15⟩, .inclusion, 15, 11, "inclusion"⟩,
  ⟨⟨16⟩, .inclusion, 16, 14, "inclusion"⟩,
  ⟨⟨17⟩, .inclusion, 17, 14, "inclusion"⟩,
  ⟨⟨15⟩, .parent, 15, 14, "parent"⟩]

abbrev support (context : Fin 28) : Support where
  classCount := 28
  mapCount := 34
  classId := fun v => ⟨v.val⟩
  mapRef := maps
  context := context
  integer := fun v => v == 27

set_option maxHeartbeats 2000000 in
theorem support_resolved (c : Fin 28) : (support c).Resolved Telematics.Structural.ast := by
  constructor
  · intro v; fin_cases v <;> simp [AST.Known, Telematics.Structural.entries, Telematics.Structural.decl]
  · intro e; fin_cases e <;> simp [Support.MapResolved, support, maps,
      Telematics.Structural.entries, Telematics.Structural.decl, Reference.target]
  · intro v h; fin_cases v <;> simp_all [support, Telematics.Structural.entries, Telematics.Structural.decl]

def head2 {c Γ} (x : Expr (support c) Γ (.collection (.objects 1))) :
    Expr (support c) Γ (.collection (.objects 2)) := .image x (.map 0)
def head3 {c Γ} (x : Expr (support c) Γ (.collection (.objects 2))) :
    Expr (support c) Γ (.collection (.objects 3)) := .image x (.map 1)
def head4 {c Γ} (x : Expr (support c) Γ (.collection (.objects 2))) :
    Expr (support c) Γ (.collection (.objects 4)) := .image x (.map 2)
def head5 {c Γ} (x : Expr (support c) Γ (.collection (.objects 1))) :
    Expr (support c) Γ (.collection (.objects 5)) := .image x (.map 3)
def head6 {c Γ} (x : Expr (support c) Γ (.collection (.objects 5))) :
    Expr (support c) Γ (.collection (.objects 6)) := .image x (.map 4)
def head7 {c Γ} (x : Expr (support c) Γ (.collection (.objects 6))) :
    Expr (support c) Γ (.collection (.objects 7)) := .image x (.map 5)
def head9 {c Γ} (x : Expr (support c) Γ (.collection (.objects 8))) :
    Expr (support c) Γ (.collection (.objects 9)) := .image x (.map 6)
def head12 {c Γ} (x : Expr (support c) Γ (.collection (.objects 11))) :
    Expr (support c) Γ (.collection (.objects 12)) := .image x (.map 7)
def head13 {c Γ} (x : Expr (support c) Γ (.collection (.objects 11))) :
    Expr (support c) Γ (.collection (.objects 13)) := .image x (.map 8)
def head15 {c Γ} (x : Expr (support c) Γ (.collection (.objects 14))) :
    Expr (support c) Γ (.collection (.objects 15)) := .image x (.map 9)
def head16 {c Γ} (x : Expr (support c) Γ (.collection (.objects 0))) :
    Expr (support c) Γ (.collection (.objects 16)) := .image x (.map 10)
def head17 {c Γ} (x : Expr (support c) Γ (.collection (.objects 0))) :
    Expr (support c) Γ (.collection (.objects 17)) := .image x (.map 11)
def head18 {c Γ} (x : Expr (support c) Γ (.collection (.objects 17))) :
    Expr (support c) Γ (.collection (.objects 18)) := .image x (.map 12)
def head19 {c Γ} (x : Expr (support c) Γ (.collection (.objects 0))) :
    Expr (support c) Γ (.collection (.objects 19)) := .image x (.map 13)
def head20 {c Γ} (x : Expr (support c) Γ (.collection (.objects 19))) :
    Expr (support c) Γ (.collection (.objects 20)) := .image x (.map 14)
def head21 {c Γ} (x : Expr (support c) Γ (.collection (.objects 20))) :
    Expr (support c) Γ (.collection (.objects 21)) := .image x (.map 15)
def head22 {c Γ} (x : Expr (support c) Γ (.collection (.objects 20))) :
    Expr (support c) Γ (.collection (.objects 22)) := .image x (.map 16)
def head23 {c Γ} (x : Expr (support c) Γ (.collection (.objects 19))) :
    Expr (support c) Γ (.collection (.objects 23)) := .image x (.map 17)
def head24 {c Γ} (x : Expr (support c) Γ (.collection (.objects 19))) :
    Expr (support c) Γ (.collection (.objects 24)) := .image x (.map 18)
def head25 {c Γ} (x : Expr (support c) Γ (.collection (.objects 24))) :
    Expr (support c) Γ (.collection (.objects 25)) := .image x (.map 19)
def head26 {c Γ} (x : Expr (support c) Γ (.collection (.objects 24))) :
    Expr (support c) Γ (.collection (.objects 26)) := .image x (.map 20)
def head27 {c Γ} (x : Expr (support c) Γ (.collection (.objects 0))) :
    Expr (support c) Γ (.collection (.objects 27)) := .image x (.map 21)
def dereference6 {c Γ} (x : Expr (support c) Γ (.collection (.objects 6))) :
    Expr (support c) Γ (.collection (.objects 27)) := .image x (.map 22)
def dereference9 {c Γ} (x : Expr (support c) Γ (.collection (.objects 9))) :
    Expr (support c) Γ (.collection (.objects 27)) := .image x (.map 23)
def dereference12 {c Γ} (x : Expr (support c) Γ (.collection (.objects 12))) :
    Expr (support c) Γ (.collection (.objects 10)) := .image x (.map 24)
def dereference18 {c Γ} (x : Expr (support c) Γ (.collection (.objects 18))) :
    Expr (support c) Γ (.collection (.objects 16)) := .image x (.map 25)
def inclusion10 {c} : Widen (support c) 10 8 := .inclusion 26 rfl
def inclusion11 {c} : Widen (support c) 11 8 := .inclusion 27 rfl
def inclusion13 {c} : Widen (support c) 13 1 := .inclusion 28 rfl
def inclusion14 {c} : Widen (support c) 14 10 := .inclusion 29 rfl
def inclusion15 {c} : Widen (support c) 15 11 := .inclusion 30 rfl
def inclusion16 {c} : Widen (support c) 16 14 := .inclusion 31 rfl
def inclusion17 {c} : Widen (support c) 17 14 := .inclusion 32 rfl
def parent15 {c Γ} (x : Expr (support c) Γ (.collection (.objects 15))) :
    Expr (support c) Γ (.collection (.objects 14)) := .image x (.map 33)

-- Head selection is explicit: fixed belongs to cache.size before dereferencing.
-- [impl->req~clafer-appendix-f-expressions~1]
def c01 : Expr (support 1) [] .boolean :=
  (Expr.and (head3 (head2 .this)).some (head5 .this).some).implies
    (head7 (head6 (head5 .this))).some

def version {c Γ} (x : Expr (support c) Γ (.collection (.objects 8))) :
    Expr (support c) Γ .integer := .integerOf rfl (dereference9 (head9 x))

def c02 : Expr (support 11) [] .boolean :=
  (version (.widenObjects inclusion11 .this)).ge
    (version (.widenObjects inclusion10 (dereference12 (head12 .this))))

def inheritedCache {Γ} : Expr (support 15) Γ (.collection (.objects 5)) :=
  head5 (.widenObjects inclusion13 (head13 (.widenObjects inclusion15 .this)))

def c03 : Expr (support 15) [] .boolean := inheritedCache.no

def c04 : Expr (support 15) [] .boolean :=
  .equal (dereference12 (head12 (.widenObjects inclusion15 .this)))
    (.widenObjects inclusion14 (parent15 .this))

def c05 : Expr (support 19) [] .boolean :=
  (head22 (head20 .this)).some.iff (Expr.extent 17).some

def displays1 {c Γ} : Expr (support c) Γ (.collection (.objects 15)) :=
  head15 (.widenObjects inclusion16 (.extent 16))

def displays2 {c Γ} : Expr (support c) Γ (.collection (.objects 15)) :=
  head15 (.widenObjects inclusion17 (.extent 17))

def exactlyTwo {c Γ x} (a : Expr (support c) Γ (.collection (.objects x))) :
    Expr (support c) Γ .boolean := .equal (.cardinality a) (.integer 2)

def c06 : Expr (support 19) [] .boolean :=
  (head23 .this).some.iff (exactlyTwo displays1)

def c07 : Expr (support 19) [] .boolean :=
  (head23 .this).some.iff ((Expr.extent 17).some.implies (exactlyTwo displays2))

def allSizes {c Γ} : Expr (support c) Γ (.collection (.objects 2)) :=
  head2 (.widenObjects inclusion13
    (head13 (.widenObjects inclusion15 (head15 (.extent 14)))))

def c08 : Expr (support 19) [] .boolean :=
  (head26 (head24 .this)).some.iff (.not (head3 allSizes).some)

def c09 : Expr (support 19) [] .boolean :=
  (head25 (head24 .this)).some.iff (.not (head4 allSizes).some)

def c10 : Expr (support 0) [] .boolean := (head22 (head20 (.extent 19))).some
def c11 : Expr (support 0) [] .boolean := (head23 (.extent 19)).some
def c12 : Expr (support 0) [] .boolean := (head26 (head24 (.extent 19))).some

def inventory : Fin 12 → Constraint :=
  ![⟨support 1, [], c01⟩, ⟨support 11, [], c02⟩,
    ⟨support 15, [], c03⟩, ⟨support 15, [], c04⟩,
    ⟨support 19, [], c05⟩, ⟨support 19, [], c06⟩,
    ⟨support 19, [], c07⟩, ⟨support 19, [], c08⟩,
    ⟨support 19, [], c09⟩, ⟨support 0, [], c10⟩,
    ⟨support 0, [], c11⟩, ⟨support 0, [], c12⟩]

theorem inventory_resolved (i : Fin 12) :
    (inventory i).support.Resolved Telematics.Structural.ast := by
  fin_cases i <;> exact support_resolved _

end Clafer.Examples.Telematics.Expressions
