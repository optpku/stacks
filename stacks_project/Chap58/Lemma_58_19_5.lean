module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleDualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

/- Lemma 58.19.5 (1): in Situation 58.19.1, the dualizing-complex and
henselian hypotheses together with either stated criterion imply fullness of
finite étale restriction along `principalQuotientMap f`. -/
@[stacks 0EK5] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_full_of_henselian_dualizing :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (f : IsLocalRing.maximalIdeal A)
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
      , (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Full)

/- Lemma 58.19.5 (2): in Situation 58.19.1, the dualizing-complex and
henselian hypotheses together with either stated criterion imply faithfulness
of finite étale restriction along `principalQuotientMap f`. -/
@[stacks 0EK5] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_henselian_dualizing :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (f : IsLocalRing.maximalIdeal A)
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
      , (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)
