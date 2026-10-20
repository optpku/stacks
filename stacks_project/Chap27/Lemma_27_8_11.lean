module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCheckRecall

/-!
# Lemma 27.8.11

The valuative criterion for the structural morphism from `Proj` to its degree-zero spectrum.

@stack 01MF
-/

@[expose] public section

open AlgebraicGeometry

universe uA uσ

section

variable {A : Type uA} [CommRing A]
variable {σ : Type uσ} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [Algebra.FiniteType (𝒜 0) A]

/- Lemma 27.8.11: Let `S` be a graded ring. If `S` is finitely generated as an algebra
over `S₀`, then `Proj(S) → Spec(S₀)` satisfies the existence and uniqueness parts of the
valuative criterion. -/
@[stacks 01MF] #check
  (AlgebraicGeometry.Proj.valuativeCriterion_existence 𝒜 :
    AlgebraicGeometry.ValuativeCriterion.Existence
      (AlgebraicGeometry.Proj.toSpecZero 𝒜))

#check
  (AlgebraicGeometry.IsSeparated.valuativeCriterion
    (AlgebraicGeometry.Proj.toSpecZero 𝒜) :
    AlgebraicGeometry.ValuativeCriterion.Uniqueness
      (AlgebraicGeometry.Proj.toSpecZero 𝒜))

end
