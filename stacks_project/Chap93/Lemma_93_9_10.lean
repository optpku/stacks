module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap93.Lemma_93_9_10_Comparison

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

/-- Lemma 93.9.10
In Situation 93.9.9 there is an equivalence
`deformationCategory Λ k hX ⥤ᵇ ringDeformationPullback Λ k c hX`
of deformation categories, obtained by open restriction and translation along
affine global sections. -/
@[stacks 0DYZ, instance]
instance instIsEquivalence_glueingBasedFunctor :
    BasedFunctor.IsEquivalence (glueingBasedFunctor Λ k c hX) :=
  sorry

/-- The glueing functor of deformation categories lies strictly over
`ArtinianLocalAlgCat`. -/
theorem glueingBasedFunctor_comp_forget :
    (glueingBasedFunctor Λ k c hX).toFunctor.comp (ringDeformationPullback Λ k c hX).p =
      schemeForget Λ k hX :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
