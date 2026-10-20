/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.SectionRingProj.RatioOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 28.28.2: an ample section-ring projective morphism maps its source into the degree-one
ratio open. -/
@[stacks 01QI] #check
  (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.preimage_projTwistRatioOpen_one_eq_top :
    ∀ {X : Scheme.{u}} {L : X.Modules}
      [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)},
      Scheme.Modules.IsSectionRingProjMap L f →
        f ⁻¹ᵁ projTwistRatioOpen (RingedSpace.GradedSections.grading L) 1 = ⊤)

/- The ratio open is the greatest open on which the corresponding twists are invertible and
their multiplication maps are isomorphisms. -/
#check
  (AlgebraicGeometry.projTwistRatioOpen_isGreatest :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (T : Proj.AssociatedModule.TwistMultiplication 𝒜) {d : ℕ},
      0 < d →
        IsGreatest
          {W : (Proj 𝒜).Opens |
            Proj.AssociatedModule.TwistMultiplication.IsGoodOpen 𝒜 T d W}
          (projTwistRatioOpen 𝒜 d))

/- Every degree of a canonical comparison along an ample section-ring projective morphism is an
isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.comparison_component_isIso :
    ∀ {X : Scheme.{u}} {L : X.Modules}
      [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)},
      Scheme.Modules.IsSectionRingProjMap L f →
        ∀ (P : ProjTwistPresentation (RingedSpace.GradedSections.grading L))
          (c : Scheme.Modules.SectionRingProjComparison L P f),
          c.IsCanonical → ∀ n : ℤ, IsIso (c.component n))
