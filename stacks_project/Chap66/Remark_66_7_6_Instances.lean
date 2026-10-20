/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.LocalProperty.Examples
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing.Examples
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
import StacksCheckRecall

@[expose] public section

universe u

open scoped ENat

/- Remark 66.7.6: étale-locality of the nine stalk properties. -/
@[stacks 0BBL] #check (AlgebraicGeometry.ofLocalRing_isNoetherianRing_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ IsNoetherianRing R).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_ringKrullDim_isEtaleLocal :
  ∀ (d : WithBot ℕ∞),
    (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isRegularLocalRing_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ IsRegularLocalRing R).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isDiscreteValuationRing_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing LocalRingProperty.isDiscreteValuationLocalRing).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isReduced_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ _root_.IsReduced R).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isNormalRing_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ IsNormalRing R).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isNoetherianOfDepth_isEtaleLocal :
  ∀ (k : ℕ),
    (AlgebraicGeometry.GermProperty.ofLocalRing (LocalRingProperty.isNoetherianOfDepth k)).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isNoetherianCohenMacaulay_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing LocalRingProperty.isNoetherianCohenMacaulay).IsEtaleLocal)

#check (AlgebraicGeometry.ofLocalRing_isGorensteinLocalRing_isEtaleLocal :
  (AlgebraicGeometry.GermProperty.ofLocalRing fun R ↦ IsGorensteinLocalRing R).IsEtaleLocal)

#check (AlgebraicGeometry.AlgebraicSpace.RegularAt.iff_exists :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.RegularAt X x ↔
      AlgebraicGeometry.AlgebraicSpace.localRingHas (fun R ↦ IsRegularLocalRing R) X x)
