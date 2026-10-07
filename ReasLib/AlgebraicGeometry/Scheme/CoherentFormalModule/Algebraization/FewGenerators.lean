module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module on the complement of a closed subset cut out up to radical by
`d` elements extends to the ambient affine scheme under the dualizing and depth hypotheses. -/
theorem extendsTo_of_fewGenerators
    {A : Type u} [CommRing A] [IsNoetherianRing A]
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
                  δ) :
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F := sorry

/-- If the defining ideal is adically complete, the same hypotheses identify the formal module
with the completion of a coherent module on the open complement. -/
theorem isCompletion_of_fewGenerators
    {A : Type u} [CommRing A] [IsNoetherianRing A]
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
                  δ) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
