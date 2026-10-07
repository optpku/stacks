module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FewGenerators
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Proposition 52.22.4 (Algebraization for ideals with few generators) (1):
the generator-bound extension criterion is owned by the reusable algebraization API. -/
@[stacks 0EJN]
#check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.extendsTo_of_fewGenerators :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (hd : 1 ≤ d) (f : Fin d → A)
    (h_zeroLocus :
      PrimeSpectrum.zeroLocus (S.I : Set A) =
        PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set A))
    (h_alternative :
      SatisfiesInequalities S F ((d : ℤ) + 1) ((d : ℤ) + 2) ∨
        ∀ y : S.Y, (hy : S.y y ∈ S.U) →
          let yU := closedFiberOpenPoint S y hy
          ∀ p : PrimeSpectrum (completedLocalRing S yU),
            p ∉ PrimeSpectrum.zeroLocus
                (completedIdeal S yU : Set (completedLocalRing S yU)) →
              let depth : EInt := enatToEInt <|
                moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
              let δ : EInt := enatToEInt (algebraizationDistance S y)
              (((d : ℤ) + 2 : ℤ) : EInt) <
                depth +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) +
                  δ),
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F)

/- Proposition 52.22.4 (Algebraization for ideals with few generators) (2):
the complete-ring consequence is owned by the reusable algebraization API. -/
@[stacks 0EJN]
#check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_fewGenerators :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (hd : 1 ≤ d) (f : Fin d → A)
    (h_zeroLocus :
      PrimeSpectrum.zeroLocus (S.I : Set A) =
        PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set A))
    (h_alternative :
      SatisfiesInequalities S F ((d : ℤ) + 1) ((d : ℤ) + 2) ∨
        ∀ y : S.Y, (hy : S.y y ∈ S.U) →
          let yU := closedFiberOpenPoint S y hy
          ∀ p : PrimeSpectrum (completedLocalRing S yU),
            p ∉ PrimeSpectrum.zeroLocus
                (completedIdeal S yU : Set (completedLocalRing S yU)) →
              let depth : EInt := enatToEInt <|
                moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
              let δ : EInt := enatToEInt (algebraizationDistance S y)
              (((d : ℤ) + 2 : ℤ) : EInt) <
                depth +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) +
                  δ),
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
