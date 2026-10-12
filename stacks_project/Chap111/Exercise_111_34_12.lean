/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.34.12: let `k` be an algebraically closed field, and let
`f : X ⟶ Y` be a morphism of projective varieties over `k` such that
`f.left ⁻¹' {y}` is finite for every closed point `y` of `Y`. Then `f` is
finite as a morphism of schemes. Hints: (a) being finite is a local property,
(b) try to reduce to Exercise 111.34.11, and (c) use a closed immersion
`X ⟶ P^n_k` to get a closed immersion `X ⟶ P^n_Y` over `Y`. -/
@[stacks 0EG7] #check
  (AlgebraicGeometry.ProjectiveVariety.isFinite_of_finite_closedPoint_fibers :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {X Y : SchemeOverField k}
      [ProjectiveVariety X] [ProjectiveVariety Y] (f : X ⟶ Y),
      (∀ y ∈ closedPoints Y.left, (f.left ⁻¹' {y}).Finite) → IsFinite f.left)
