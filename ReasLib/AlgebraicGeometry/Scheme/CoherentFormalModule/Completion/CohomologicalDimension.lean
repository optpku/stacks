/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For local-cohomological dimension one, the ordinary `(2, 3)` inequalities are
equivalent to the strict depth, quotient-dimension, and distance bound. -/
theorem inequalities_iff_depth_dimension_gt_three (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1) :
    SatisfiesInequalities S F 2 3 ↔
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        let yU := closedFiberOpenPoint S y hy
        ∀ p : PrimeSpectrum (completedLocalRing S yU),
          p ∉ PrimeSpectrum.zeroLocus
            (completedIdeal S yU : Set (completedLocalRing S yU)) →
            let depth : EInt := enatToEInt <|
              moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
            let δ : EInt := enatToEInt (algebraizationDistance S y)
            (3 : EInt) < depth +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ := sorry

/-- For a local base with maximal ideal `S.a`, the ordinary `(2, 3)` inequalities
are equivalent to a strict depth and quotient-dimension bound at
one-dimensional points of the closed fiber. -/
theorem inequalities_iff_depth_dimension_gt_two_of_localRing
    [IsLocalRing A]
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1) :
    SatisfiesInequalities S F 2 3 ↔
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        topologicalKrullDim (closure ({y} : Set S.Y)) = 1 →
          let yU := closedFiberOpenPoint S y hy
          ∀ p : PrimeSpectrum (completedLocalRing S yU),
            p ∉ PrimeSpectrum.zeroLocus
              (completedIdeal S yU : Set (completedLocalRing S yU)) →
                let depth : EInt := enatToEInt <|
                  moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
                (2 : EInt) < depth +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
