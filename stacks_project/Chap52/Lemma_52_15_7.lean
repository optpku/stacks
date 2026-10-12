/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Proposition_52_12_3
public import stacks_project.Chap52.Lemma_52_15_2
public import stacks_project.Chap52.«52_8_0_1_AssociatedSubset»
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.RingTheory.Ideal.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Lemma 52.15.7: for nested ideals `I ≤ 𝔞` in a Noetherian ring `A`, if `A` is
`I`-adically complete, has a dualizing complex, and the stated associated-prime
dimension bound holds along `V(𝔞)`, neighborhood completion on `U = Spec(A) ∖ V(𝔞)`
is fully faithful on finite locally free coherent modules. -/
@[stacks 0EKU]
theorem neighborhoodCompletionFullyFaithful_of_associatedPrimeDimension
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ associatedPrimes A A →
        ¬ S.I ≤ p.asIdeal →
          p ∉ PrimeSpectrum.associatedSubset S.I S.a →
            q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (S.a : Set A) →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q))) :
    CoherentCompletion.NeighborhoodCompletionFullyFaithful
      (AffineAlgebraizationSetup.idealOnOpen S) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
