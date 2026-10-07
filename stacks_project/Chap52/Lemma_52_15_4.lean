module

public import stacks_project.Chap52.Lemma_52_12_4
public import stacks_project.Chap52.Lemma_52_15_1
public import stacks_project.Chap52.«52_8_0_1_AssociatedSubset»
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.Ideal.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open scoped ENat

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Lemma 52.15.4: for nested ideals `I ≤ 𝔞` in a Noetherian ring `A`, if `A` is
`I`-adically complete, has a dualizing complex, and satisfies the stated dimension
and depth bounds in the two associated-subset cases, completion on
`U = Spec(A) ∖ V(𝔞)` is fully faithful on finite locally free coherent modules. -/
@[stacks 0EKQ]
theorem completionFullyFaithful_of_associatedPrimeDimension
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
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_depth : ∀ p : PrimeSpectrum A,
      ¬ S.I ≤ p.asIdeal →
        p ∈ PrimeSpectrum.associatedSubset S.I S.a →
          (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal A)) :
    Nonempty (Scheme.CoherentCompletion.onFiniteLocallyFree
      (idealOnOpen S)).FullyFaithful := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
