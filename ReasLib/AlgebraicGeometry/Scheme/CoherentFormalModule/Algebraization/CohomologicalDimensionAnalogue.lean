/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- The cohomological-dimension analogue of the universal extension assertion for coherent formal
modules on an open complement of an affine scheme. -/
def cohomologicalDimensionAnalogue_extends : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I (d : ℤ))
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
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F

/-- The cohomological-dimension analogue of the universal completion assertion for coherent formal
modules when the defining ideal is adically complete. -/
def cohomologicalDimensionAnalogue_isCompletion : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A),
        CategoryTheory.DerivedCategory.IsDualizing K)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (d : ℕ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I (d : ℤ))
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
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F

end AlgebraicGeometry.Scheme.CoherentFormalModules
