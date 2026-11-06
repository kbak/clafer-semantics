import Clafer.Constraints.Empty

open Clafer.Constraints

-- Contextual instantiation works for every element class and both core arities.
-- [proof->req~clafer-core-typing~1]
example {s : Support} {Γ} (x y : s.Vertex) :
    Expr s Γ (.collection (.relation x y)) := .empty (.relation x y)

-- A unary literal cannot become a relation, Boolean, or scalar by inference.
example {s : Support} {_Γ : List (Local s)} (_x _y : s.Vertex) : True := by
  fail_if_success have _ : Expr s _Γ (.collection (.relation _x _y)) := Expr.empty (.objects _x)
  fail_if_success have _ : Expr s _Γ .boolean := Expr.empty (.objects _x)
  fail_if_success have _ : Expr s _Γ .integer := Expr.empty (.objects _x)
  trivial
