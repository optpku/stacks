/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

import stacks_project.Chap55.Example_55_10_3_Conic

open AlgebraicGeometry.SplitConic

example : projectionCoordinates false 0 = 0 := rfl
example : projectionCoordinates false 1 = 1 := rfl
example : projectionCoordinates true 0 = 0 := rfl
example : projectionCoordinates true 1 = 2 := rfl

example (R : Type) [CommRing R] (π : R) :
    equation R π = MvPolynomial.X 1 * MvPolynomial.X 2 -
      MvPolynomial.C π * MvPolynomial.X 0 ^ 2 := rfl

example (R : Type) [CommRing R] (π : R) (second : Bool) (i : Fin 2) :
    projectionRingHom R π second (MvPolynomial.X i) =
      Ideal.Quotient.mk (equationIdeal R π).toIdeal
        (MvPolynomial.X (projectionCoordinates second i)) := by
  simp [projectionRingHom]
