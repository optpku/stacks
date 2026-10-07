module

public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth
public import stacks_project.Chap58.Lemma_58_19_2
public import stacks_project.Chap58.Lemma_58_21_6_Purity

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- The Lemma 58.23.1 alternative: either `A_f` is `(S₂)` with every irreducible
component of `X` not contained in `X₀` of dimension at least `4`, or the
primewise depth-dimension inequality holds off `V(f)`. -/
def dualizingCompleteNeighborhoodAlternative : Prop :=
  (SerreConditionS (Localization.Away (f : A)) 2 ∧
    ∀ p : PrimeSpectrum A,
      p.asIdeal ∈ minimalPrimes A →
        (f : A) ∉ p.asIdeal →
          (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
  (∀ p : PrimeSpectrum A,
    p ∉ PrimeSpectrum.zeroLocus ({(f : A)} : Set A) →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus ({(f : A)} : Set A) ≠
        {closedPoint A} →
        (3 : EInt) <
          ((WithTop.map Int.ofNat
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
            WithBot.map (WithTop.map Int.ofNat)
              (ringKrullDim (A ⧸ p.asIdeal)))

/-- Unfolds the Lemma 58.23.1 alternative. -/
theorem dualizingCompleteNeighborhoodAlternative_iff :
    dualizingCompleteNeighborhoodAlternative f ↔
      (SerreConditionS (Localization.Away (f : A)) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (f : A) ∉ p.asIdeal →
              (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus ({(f : A)} : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus ({(f : A)} : Set A) ≠
            {closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal))) := sorry

/-- Purity of `(A_f)_p` at every maximal ideal `p` of `A_f`. -/
def hasPurityAtMaximalsAway : Prop :=
  ∀ (p : Ideal (Localization.Away (f : A))) [p.IsPrime],
    p.IsMaximal → HasPurity (Localization.AtPrime p)

/-- Unfolds maximal-ideal purity of localizations of `A_f`. -/
theorem hasPurityAtMaximalsAway_iff :
    hasPurityAtMaximalsAway f ↔
      ∀ (p : Ideal (Localization.Away (f : A))) [p.IsPrime],
        p.IsMaximal → HasPurity (Localization.AtPrime p) := sorry

/-- Lemma 58.24.1: in Situation 58.19.1, if `A` has a dualizing complex and is
`f`-adically complete, either `A_f` is `(S₂)` with every irreducible component of
`X` not contained in `X₀` of dimension at least `4` or the primewise
depth-dimension inequality holds off `V(f)`, and purity holds at `(A_f)_p` for
every maximal ideal `p` of `A_f`, then the restriction functor
`FÉt_U ⟶ FÉt_{U₀}` identified with
`Scheme.finiteEtaleBaseChange (principalQuotientMap f)` is essentially
surjective. -/
@[stacks 0EK9, instance]
instance finiteEtaleBaseChange_essSurj_of_dualizing_complete_purity
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [IsAdicComplete (principalIdeal f) A]
    [Fact (dualizingCompleteNeighborhoodAlternative f)]
    [Fact (hasPurityAtMaximalsAway f)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj := sorry

end AlgebraicGeometry.PuncturedSpectrum
