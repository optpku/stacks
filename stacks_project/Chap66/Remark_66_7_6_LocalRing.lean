/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.LocalProperty
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 66.7.6: stalkwise construction from an invariant property of local rings. -/
@[stacks 0BBL] #check (AlgebraicGeometry.GermProperty.ofLocalRing.isEtaleLocal :
  ∀ {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop},
    LocalRingProperty.RespectsIso P → LocalRingProperty.IsEtaleLocalAtPrimes P →
      (AlgebraicGeometry.GermProperty.ofLocalRing P).IsEtaleLocal)

#check (AlgebraicGeometry.GermProperty.ofLocalRing :
  (∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) →
    AlgebraicGeometry.GermProperty.{u})

#check (AlgebraicGeometry.AlgebraicSpace.localRingHas :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicGeometry.AlgebraicSpace S) (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    Prop)
