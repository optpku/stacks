/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower

/-!
# Coordinates on tensor powers
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The `i`-th coordinate projection of the degree-`n` cartesian tensor power of a
scheme over a field. -/
noncomputable def coord (X : SchemeOverField k) :
    (n : ℕ) → Fin n → (tensorPower X n ⟶ X)
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      i.cases (fst X (tensorPower X n))
        (fun j ↦ snd X (tensorPower X n) ≫ coord X n j)

/-- The zeroth coordinate of a successor tensor power is the cartesian first
projection. -/
theorem coord_zero (X : SchemeOverField k) (n : ℕ) :
    coord X (n + 1) 0 = fst X (tensorPower X n) :=
  sorry

/-- A successor coordinate of a successor tensor power factors through the cartesian
second projection. -/
theorem coord_succ (X : SchemeOverField k) (n : ℕ) (i : Fin n) :
    coord X (n + 1) i.succ = snd X (tensorPower X n) ≫ coord X n i :=
  sorry

/-- The pair of coordinates `(x, x_{i+1})` as a morphism `tensorPower X (r + 1) ⟶ X ⊗ X`. -/
noncomputable def pairCoord (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    tensorPower X (r + 1) ⟶ X ⊗ X :=
  lift (coord X (r + 1) 0) (coord X (r + 1) i.succ)

/-- The first factor of `pairCoord` is the zeroth coordinate. -/
theorem pairCoord_fst (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    pairCoord X r i ≫ fst X X = coord X (r + 1) 0 :=
  sorry

/-- The second factor of `pairCoord` is the `(i + 1)`-st coordinate. -/
theorem pairCoord_snd (X : SchemeOverField k) (r : ℕ) (i : Fin r) :
    pairCoord X r i ≫ snd X X = coord X (r + 1) i.succ :=
  sorry

end AlgebraicGeometry.SchemeOverField
