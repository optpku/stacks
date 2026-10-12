/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 27.10.4: for a positive degree, the union of the opens `D₊(f * g)` for homogeneous
elements whose degrees differ by that degree is the greatest open on which the corresponding
canonical twists are invertible and their multiplication maps are isomorphisms. -/
@[stacks 01MU] #check
  (AlgebraicGeometry.projTwistRatioOpen_isGreatest :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜)
      {d : ℕ}, 0 < d →
        IsGreatest
          {W : (AlgebraicGeometry.Proj 𝒜).Opens |
            AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication.IsGoodOpen
              𝒜 T d W}
          (AlgebraicGeometry.projTwistRatioOpen 𝒜 d))

/- On the same ratio open, the canonical comparison between a graded module's associated sheaf
tensored with a twist and the associated sheaf of the shifted grading is an isomorphism at every
multiple of the positive degree. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictRatioOpen_isIso :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {M : Type u} [AddCommGroup M] [Module A M]
      (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
      (C : AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
      {d : ℕ}, 0 < d → ∀ n : ℤ,
        IsIso
          (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictOpenMap
            𝒜 ℳ C (AlgebraicGeometry.projTwistRatioOpen 𝒜 d) (n * (d : ℤ))))
