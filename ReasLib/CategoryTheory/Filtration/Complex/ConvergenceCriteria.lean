/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence

/-!
# Stagewise Criteria for Filtered-Complex Convergence

@stack 0BK5

Eventual vanishing of stage cohomology above and eventual stabilization below give boundedness,
finite induced cohomology filtrations, and convergence of an associated spectral sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredComplex
namespace StageCohomology

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In each degree, the cohomology of sufficiently high filtration stages vanishes. -/
@[stacks 0BK5, stacks 0H7W "eventual vanishing of filtration-stage cohomology"]
def eventuallyVanishesAbove (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p → IsZero ((K.stage p).homology n)

/-- In each degree, sufficiently low filtration stages induce an isomorphism on cohomology. -/
@[stacks 0BK5, stacks 0H7W "eventual stabilization of filtration-stage cohomology"]
def eventuallyStabilizesBelow (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ → IsIso (K.cohomologyMap p n)

/-- Eventual acyclicity of stage complexes implies eventual vanishing of their cohomology. -/
@[stacks 0H7W "high-stage acyclicity gives eventual cohomology vanishing"]
theorem eventuallyVanishesAbove_of_acyclic (K : FilteredComplex C)
    (hAcyclic : ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p → (K.stage p).Acyclic) :
    eventuallyVanishesAbove K := sorry

/-- Eventual quasi-isomorphism of stage inclusions implies eventual stabilization on cohomology. -/
@[stacks 0H7W "low-stage quasi-isomorphisms give cohomology stabilization"]
theorem eventuallyStabilizesBelow_of_quasiIso
    (K : FilteredComplex C)
    (hQuasi : ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ → QuasiIso (K.stageInclusion p)) :
    eventuallyStabilizesBelow K := sorry

/-- The stagewise vanishing and stabilization criteria make every associated spectral sequence
bounded. -/
@[stacks 0BK5, stacks 0H7W "boundedness from eventual stage cohomology"]
theorem associated_isBounded
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hvanish : eventuallyVanishesAbove K)
    (hstabilize : eventuallyStabilizesBelow K) :
    E.IsBounded := sorry

/-- The stagewise vanishing and stabilization criteria make all induced cohomology filtrations
finite. -/
@[stacks 0BK5, stacks 0H7W "finite cohomology filtrations from eventual stage cohomology"]
theorem Cohomology.isFinite
    (K : FilteredComplex C) (hvanish : eventuallyVanishesAbove K)
    (hstabilize : eventuallyStabilizesBelow K) :
    Cohomology.Filtration.IsFinite K := sorry

/-- The stagewise criteria imply abutment of an associated spectral sequence to cohomology. -/
@[stacks 0BK5 "abutment from eventual stage cohomology"]
theorem associated_abuts
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hvanish : eventuallyVanishesAbove K)
    (hstabilize : eventuallyStabilizesBelow K) :
    Cohomology.Convergence.Abuts K E := sorry

/-- The stagewise vanishing and stabilization criteria imply convergence of every associated
spectral sequence to cohomology. -/
@[stacks 0BK5, stacks 0H7W "convergence from eventual stage cohomology"]
theorem associated_converges
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (hvanish : eventuallyVanishesAbove K)
    (hstabilize : eventuallyStabilizesBelow K) :
    Cohomology.Convergence.Converges K E := sorry

end StageCohomology
end FilteredComplex
end CategoryTheory
