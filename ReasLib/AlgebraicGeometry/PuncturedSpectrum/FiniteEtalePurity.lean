module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

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

/-- Either localization away from an element satisfies `(S₂)` and every minimal
component not containing it has dimension at least four, or every prime outside
its zero locus whose closure meets that locus beyond the closed point has depth
plus quotient dimension greater than three. -/
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

/-- The neighborhood alternative is equivalent to the explicit disjunction of
the Serre and component-dimension conditions with the restricted primewise
depth-dimension inequality. -/
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
                  (ringKrullDim (A ⧸ p.asIdeal))) := Iff.rfl

/-- Purity of `(A_f)_p` at every maximal ideal `p` of `A_f`. -/
def hasPurityAtMaximalsAway : Prop :=
  ∀ (p : Ideal (Localization.Away (f : A))) [p.IsPrime],
    p.IsMaximal → HasPurity (Localization.AtPrime p)

/-- Purity at maximal localizations away from an element is equivalent to purity
at the localization of each maximal ideal of that localization. -/
theorem hasPurityAtMaximalsAway_iff :
    hasPurityAtMaximalsAway f ↔
      ∀ (p : Ideal (Localization.Away (f : A))) [p.IsPrime],
        p.IsMaximal → HasPurity (Localization.AtPrime p) := Iff.rfl

/-- For a Noetherian local ring admitting a dualizing complex and complete along
an element of its maximal ideal, finite étale restriction to the principal-quotient
punctured spectrum is essentially surjective if the neighborhood alternative
holds and every maximal localization away from the element satisfies purity. -/
instance finiteEtaleBaseChange_essSurj_of_dualizing_complete_purity
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
    [IsAdicComplete (principalIdeal (f : A)) A]
    [Fact (dualizingCompleteNeighborhoodAlternative f)]
    [Fact (hasPurityAtMaximalsAway f)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj := sorry

/-- For a Noetherian local ring complete along a regular element of its maximal
ideal, finite étale restriction to the principal-quotient punctured spectrum is
essentially surjective if the first two local cohomology modules of the
principal quotient are finite over the ring and every maximal localization
away from the element satisfies purity. -/
instance finiteEtaleBaseChange_essSurj_of_complete_localCohomology_purity
    [IsAdicComplete (principalIdeal (f : A)) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Fact (hasPurityAtMaximalsAway f)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).EssSurj := sorry

end AlgebraicGeometry.PuncturedSpectrum
