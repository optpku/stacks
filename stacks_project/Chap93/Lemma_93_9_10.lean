/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover.Gluing

/-!
# Glueing of scheme deformation categories along two affine charts
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped BasedFunctor

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/- Lemma 93.9.10
In Situation 93.9.9 there is an equivalence
`deformationCategory Λ k hX ⥤ᵇ ringDeformationPullback Λ k c hX`
of deformation categories, obtained by open restriction and translation along
affine global sections. -/
@[stacks 0DYZ] #check
  (AlgebraicGeometry.Scheme.TwoAffineOpenCover.glueingBasedFunctor_isEquivalence Λ k c hX :
    CategoryTheory.BasedFunctor.IsEquivalence
      (AlgebraicGeometry.Scheme.TwoAffineOpenCover.glueingBasedFunctor Λ k c hX))

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
