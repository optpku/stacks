/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The composite of affine morphisms of schemes is affine. -/
theorem isAffineHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  infer_instance

end AlgebraicGeometry
