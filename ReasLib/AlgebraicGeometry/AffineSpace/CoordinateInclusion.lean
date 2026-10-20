/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The standard inclusion of relative affine spaces that preserves the first `m`
coordinates and sets the final `n` coordinates to zero. -/
def standardInclusion (m n : ℕ) (S : Scheme.{u}) :
    𝔸(ULift.{u} (Fin m); S) ⟶ 𝔸(ULift.{u} (Fin (m + n)); S) :=
  homOfVector (𝔸(ULift.{u} (Fin m); S) ↘ S) fun i ↦
    (finSumFinEquiv.symm i.down).elim
      (fun j ↦ coord S (ULift.up j)) (fun _ ↦ 0)

/-- The standard affine-space inclusion is a morphism over its base scheme. -/
theorem standardInclusion_over (m n : ℕ) (S : Scheme.{u}) :
    standardInclusion m n S ≫ (𝔸(ULift.{u} (Fin (m + n)); S) ↘ S) =
      𝔸(ULift.{u} (Fin m); S) ↘ S := sorry

/-- Pullback along the standard inclusion preserves each of the first `m` coordinates. -/
theorem standardInclusion_appTop_coord_castAdd (m n : ℕ) (S : Scheme.{u})
    (a : Fin m) :
    (standardInclusion m n S).appTop
        (coord S (ULift.up (Fin.castAdd n a))) =
      coord S (ULift.up a) := sorry

/-- Pullback along the standard inclusion sends each of the final `n` coordinates to zero. -/
theorem standardInclusion_appTop_coord_natAdd (m n : ℕ) (S : Scheme.{u})
    (b : Fin n) :
    (standardInclusion m n S).appTop
        (coord S (ULift.up (Fin.natAdd m b))) = 0 := sorry

/-- The standard coordinate inclusion of relative affine spaces is a closed immersion. -/
instance standardInclusion_isClosedImmersion (m n : ℕ) (S : Scheme.{u}) :
    IsClosedImmersion (standardInclusion m n S) := sorry

end AlgebraicGeometry.AffineSpace
