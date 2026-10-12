/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.EventualSections

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
variable (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1)
variable (ℳ : ℤ → Submodule ℤ M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite A M]
variable (comparisonIso : ∀ n : ℤ,
  ProjTwistFamily.tensorTwist (Proj.AssociatedModule.twistingSheaf 𝒜)
      (Proj.AssociatedModule.sheaf 𝒜 ℳ) n ≅
    Proj.AssociatedModule.sheaf 𝒜 (GradedModule.shiftGrading ℳ n))

/- Lemma 30.14.3: if the degree-zero part of a graded ring is Noetherian, the ring is finite type
and generated in degree one over that part, and an internally graded module is finite, then the
canonical maps from its homogeneous pieces to the global sections of its associated-sheaf twists
are isomorphisms in all sufficiently large degrees. -/
@[stacks 0AG7] #check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections.toTensorTwist_eventually_isIso
    𝒜 ℳ hgenerated comparisonIso :
      ∃ b : ℤ, ∀ n : ℤ, b ≤ n →
        IsIso
          (AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections.toTensorTwist
            𝒜 ℳ comparisonIso n))
