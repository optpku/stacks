module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import stacks_project.Chap93.Lemma_93_9_10_Restrict

/-!
# Two-fiber product of ring deformation categories

The 2-fiber product `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` of the restriction cospan
along a two-chart affine overlap.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

/-- The 2-fiber product `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` of ring deformation categories. -/
abbrev ringDeformationPullback :=
  BasedCategory.PseudoPullback (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX)

/-- The projection of `ringDeformationPullback` evaluates to the stored Artinian base. -/
theorem ringDeformationPullback_p_obj
    (P : (ringDeformationPullback Λ k c hX).obj) :
    (ringDeformationPullback Λ k c hX).p.obj P =
      BasedCategory.PseudoPullback.baseObj P :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
