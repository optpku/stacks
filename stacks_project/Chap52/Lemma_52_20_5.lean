/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.20.5: when `A` is local, `S.a` is its maximal ideal, and
`cd(A, S.I) = 1`, the `(2, 3)`-inequalities are equivalent to the strict
depth-plus-quotient-dimension bound at the dimension-one points of `U ∩ Y`. -/
@[stacks 0EJA] #check (@AlgebraicGeometry.Scheme.CoherentFormalModules.inequalities_iff_depth_dimension_gt_two_of_localRing.{u} :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (S : AffineAlgebraizationSetup A)
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
      (h_a : S.a = IsLocalRing.maximalIdeal A)
      (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1),
      SatisfiesInequalities S F 2 3 ↔
        ∀ y : S.Y, (hy : S.y y ∈ S.U) →
          topologicalKrullDim (closure ({y} : Set S.Y)) = 1 →
          have yU := closedFiberOpenPoint S y hy
          ∀ p : PrimeSpectrum (completedLocalRing S yU),
            p ∉ PrimeSpectrum.zeroLocus
              (completedIdeal S yU : Set (completedLocalRing S yU)) →
                have depth := enatToEInt <|
                  moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
                (2 : EInt) < depth +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)))

end AlgebraicGeometry.Scheme.CoherentFormalModules
