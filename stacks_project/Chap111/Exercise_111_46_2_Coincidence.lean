/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower.Coordinates
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Coincidence

/-!
# Coordinates and coincidence divisors on tensor powers

The coordinate and coincidence-divisor constructions are available from their
mathematical owners.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

universe u

#check (AlgebraicGeometry.SchemeOverField.coord :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) (n : ℕ),
    Fin n → (tensorPower X n ⟶ X))

#check (AlgebraicGeometry.SchemeOverField.coincidenceDivisor :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) (r : ℕ),
    (tensorPower X (r + 1)).left.IdealSheafData)
