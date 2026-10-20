/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Flat base change of blowups of algebraic spaces

Blowing up a closed subspace commutes with flat base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBlowup

/-- Given blowups of a closed subspace and its inverse image along a flat morphism,
there is a morphism between the blowups making the resulting square cartesian. -/
theorem exists_isPullback_of_flat {S : Scheme.{u}}
    {X₁ X₂ X₁' X₂' : AlgebraicSpace S}
    (f : X₁ ⟶ X₂) [Flat f] (Z₂ : ClosedSubspace X₂)
    (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
    [IsBlowup b₁ (Z₂.inverseImageSubspace f)] [IsBlowup b₂ Z₂] :
    ∃ g' : X₁' ⟶ X₂', CategoryTheory.IsPullback g' b₁ b₂ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBlowup
