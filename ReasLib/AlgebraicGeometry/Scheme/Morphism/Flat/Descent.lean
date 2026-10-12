/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Descent of flatness for scheme morphisms

This file records descent of flatness along flat surjective morphisms of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)

/-- If `h` is flat and surjective and the composite `h ≫ f` is flat, then `f`
is flat. -/
theorem flat_of_comp_of_surjective_of_flat
    [Flat h] [Surjective h] [Flat (h ≫ f)] :
    Flat f := sorry

/-- If `h : X ⟶ Y` is flat and surjective and the diagonal of `h ≫ f` is flat,
then the diagonal of `f : Y ⟶ Z` is flat. -/
theorem flat_diagonal_of_flat_surjective {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (f : Y ⟶ Z) [Flat h] [Surjective h]
    [Flat (pullback.diagonal (h ≫ f))] :
    Flat (pullback.diagonal f) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Flat

/-- Flatness descends under precomposition by a flat surjective morphism between affine
schemes. -/
instance hasOfPrecompFpqc :
    (CategoryTheory.MorphismProperty.inverseImage
      (@AlgebraicGeometry.Flat : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.AffineScheme.forgetToScheme).HasOfPrecompProperty
      (MorphismProperty.inverseImage
        ((@AlgebraicGeometry.Flat ⊓ @AlgebraicGeometry.Surjective) :
          MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme) := sorry

end AlgebraicGeometry.Flat
