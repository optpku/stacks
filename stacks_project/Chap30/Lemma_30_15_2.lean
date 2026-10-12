/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.FiniteSections

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
variable [IsNoetherianRing A] [DirectSum.Decomposition ℳ] [Module.Finite A M]
variable (k : ℤ)

/- Lemma 30.15.2 (1): the truncated degree-zero cohomology of the sheaves associated to the
shifted gradings of a finite graded module is finite. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.FiniteSections.shifted_finite 𝒜 ℳ k :
    Module.Finite A
      (Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k))

/- Lemma 30.15.2 (2): the truncated degree-zero cohomology of the tensor twists of the
associated sheaf of a finite graded module is finite. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.FiniteSections.tensorTwist_finite 𝒜 ℳ k :
    Module.Finite A
      (Proj.TwistedSections.Cohomology.truncated 𝒜
        (Proj.AssociatedModule.sheaf 𝒜 ℳ) k))

/- Lemma 30.15.2 (3): the canonical map from tensor-twist cohomology to the cohomology of
shifted associated sheaves is the direct sum of the degreewise canonical shift comparisons. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.ShiftComparison.Truncated.canonicalMap 𝒜 ℳ k :
      Proj.TwistedSections.Cohomology.truncated 𝒜
          (Proj.AssociatedModule.sheaf 𝒜 ℳ) k →ₗ[A]
        Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k)

#check Proj.AssociatedModule.ShiftComparison.Truncated.canonicalMap_of 𝒜 ℳ k

variable (lowerPiecesVanish : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (ℳ n)))

/- Lemma 30.15.2 (4): when all pieces below the truncation bound vanish, the homogeneous
section maps assemble to the canonical linear map from the graded module to shifted cohomology. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.ShiftedSections.Truncated.map 𝒜 ℳ k lowerPiecesVanish :
    M →ₗ[A] Proj.AssociatedModule.ShiftedSections.Cohomology.truncated 𝒜 ℳ k)

#check Proj.AssociatedModule.ShiftedSections.Truncated.map_of
  𝒜 ℳ k lowerPiecesVanish

/- Lemma 30.15.2 (5): the canonical map from each homogeneous piece to degree-zero cohomology
of its shifted associated sheaf is an isomorphism in all sufficiently large degrees. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.FiniteSections.sectionMap_eventually_isIso 𝒜 ℳ :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n →
      IsIso (AddCommGrpCat.ofHom
        ((Proj.AssociatedModule.ShiftedSections.presentation 𝒜 ℳ).cohomologyZeroSectionMap n)))

variable (G : GradedAlgebra.PositiveGenerators 𝒜)
variable (n : ℤ) (hn : (G.period : ℤ) ∣ n)

/- Lemma 30.15.2 (6): the canonical map `N_n → N'_n` on degree-zero cohomology is an
isomorphism in degrees divisible by the canonical common period of the positive generator degrees. -/
@[stacks 0B5R] #check
  (Proj.AssociatedModule.ShiftComparison.CohomologyZero.canonicalIsIso_of_period
    𝒜 ℳ G n hn :
      IsIso (RingedSpace.moduleCohomologyMap
        ((Proj.AssociatedModule.ShiftComparison.canonical 𝒜 ℳ).hom n) 0))

end AlgebraicGeometry
