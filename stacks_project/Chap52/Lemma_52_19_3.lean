/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.19.3: when `cd(A, I) = 1`, the `(2, 3)`-inequalities for a coherent
formal module are equivalent to the strict depth-plus-dimension-plus-distance bound
at every prime of each completed stalk away from the completed closed fibre. -/
@[stacks 0EKW] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.inequalities_iff_depth_dimension_gt_three :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1),
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
                (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ)

end AlgebraicGeometry.Scheme.CoherentFormalModules
