/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AffineSpace.SquareMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.SquareMorphism

/-!
# Universal homeomorphism of the affine-line involution quotient

The punctured-negation quotient has an étale locally-surjective atlas, and its
morphism to the affine line induced by squaring is a universal homeomorphism in
characteristic different from two.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The atlas `𝔸¹_k ⟶ X` is étale relative to `uliftYoneda`. -/
theorem etale_atlas (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom :=
  (sheafOfPoints_spec k).1

/-- The atlas `𝔸¹_k ⟶ X` is étale-locally surjective. -/
theorem locallySurjective_atlas (k : Type u) [Field k] [NeZero (2 : k)] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom :=
  (sheafOfPoints_spec k).2.1

/-- The composite of the atlas with `toAffineLine` is representably universally closed. -/
theorem universallyClosed_comp_atlas_toAffineLine (k : Type u) [Field k] :
    (MorphismProperty.over (@UniversallyClosed)).relative uliftYoneda.{u + 1}
      (atlas k ≫ toAffineLine k).hom := sorry

/-- The descended squaring morphism from the punctured-negation quotient to the
affine line is a universal homeomorphism in characteristic different from two. -/
theorem universalHomeomorphism_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.AlgebraicSpace.Sheaf.isUniversalHomeomorphism
      (toAffineLine k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
