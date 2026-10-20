module

public import ReasLib.RingTheory.Node.CoordinateRing
public import ReasLib.Algebra.Module.EulerPoincare
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Prod
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Euler-Poincaré functions on the node

Evaluation on the two axis quotient modules classifies Euler-Poincaré functions on
finite modules over `k[x, y] / (xy)` when `k` is algebraically closed.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory.ModuleCat

namespace NodeCoordinateRing

/-- The finite-module Grothendieck class of the quotient cutting out one axis of the node. -/
def axisClass (k : Type u) [CommRing k] (i : Fin 2) :
    K0.finite.{u, u} (Ring k) :=
  K0.finiteClass (Ring k) (Ring k ⧸ axisIdeal k i)

/-- The additive evaluation map on the two axis classes, ordered as the quotient by
`(y)` followed by the quotient by `(x)`. -/
def evalAxisPair (k : Type u) [CommRing k] :
    Module.EulerPoincareFunction.{u, u} (Ring k) →+ ℤ × ℤ :=
  (AddMonoidHom.eval (axisClass k (1 : Fin 2))).prod
    (AddMonoidHom.eval (axisClass k (0 : Fin 2)))

/-- Evaluation on an axis quotient module agrees with evaluation on its Grothendieck class. -/
theorem eval_axisClass {k : Type u} [CommRing k]
    (φ : Module.EulerPoincareFunction.{u, u} (Ring k)) (i : Fin 2) :
    Module.EulerPoincareFunction.eval φ (Ring k ⧸ axisIdeal k i) =
      φ (axisClass k i) :=
  sorry

/-- Evaluation on the axis pair gives the values on the quotient by `(y)` and the
quotient by `(x)`, in that order. -/
theorem evalAxisPair_apply {k : Type u} [CommRing k]
    (φ : Module.EulerPoincareFunction.{u, u} (Ring k)) :
    evalAxisPair k φ =
      (φ (axisClass k (1 : Fin 2)), φ (axisClass k (0 : Fin 2))) :=
  sorry

/-- Over an algebraically closed field, evaluation on the two axis classes is bijective. -/
theorem evalAxisPair_bijective {k : Type u} [Field k] [IsAlgClosed k] :
    Function.Bijective (evalAxisPair k) :=
  sorry

/-- Euler-Poincaré functions on the node over an algebraically closed field are equal
if their evaluations on the two axis classes agree. -/
theorem eq_of_evalAxisPair {k : Type u} [Field k] [IsAlgClosed k]
    {φ ψ : Module.EulerPoincareFunction.{u, u} (Ring k)}
    (h : evalAxisPair k φ = evalAxisPair k ψ) : φ = ψ :=
  sorry

/-- Every pair of integers is realized by an Euler-Poincaré function on the node over
an algebraically closed field. -/
theorem exists_evalAxisPair {k : Type u} [Field k] [IsAlgClosed k] (ab : ℤ × ℤ) :
    ∃ φ : Module.EulerPoincareFunction.{u, u} (Ring k), evalAxisPair k φ = ab :=
  sorry

end NodeCoordinateRing
