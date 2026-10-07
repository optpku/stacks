module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleCompletion
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (f : maximalIdeal A)

/-- A dualizing complex and either the Serre/minimal-component condition or the
depth-dimension condition make principal-quotient finite étale restriction full. -/
theorem finiteEtaleBaseChange_full_of_henselian_dualizing
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [HenselianRing A (principalIdeal f)]
    [Fact
      ((SerreConditionS (Localization.Away (f : A)) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (f : A) ∉ p.asIdeal →
              (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        (f : A) ∉ p.asIdeal →
          (2 : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))))] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Full := sorry

/-- A dualizing complex and either the Serre/minimal-component condition or the
depth-dimension condition make principal-quotient finite étale restriction faithful. -/
theorem finiteEtaleBaseChange_faithful_of_henselian_dualizing
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [HenselianRing A (principalIdeal f)]
    [Fact
      ((SerreConditionS (Localization.Away (f : A)) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (f : A) ∉ p.asIdeal →
              (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        (f : A) ∉ p.asIdeal →
          (2 : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))))] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

/-- For a Noetherian local ring with a dualizing complex and a henselian principal
pair, a finite étale cover of the punctured spectrum that extends over the
principal quotient extends over the whole spectrum, provided either the
Serre/minimal-component condition or the depth-dimension condition holds. -/
theorem finiteEtale_extends_of_henselian_dualizing
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [HenselianRing A (principalIdeal f)]
    [Fact
      ((SerreConditionS (Localization.Away (f : A)) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (f : A) ∉ p.asIdeal →
              (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        (f : A) ∉ p.asIdeal →
          (2 : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))))]
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0)) :
    ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

end AlgebraicGeometry.PuncturedSpectrum
