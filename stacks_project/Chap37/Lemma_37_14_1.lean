/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.SurjectivePullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.14.1: the spectra of a surjective ring-pullback situation form a
pushout square of schemes. -/
@[stacks 0ET0]
#check (SurjectiveRingPullbackSituation.schemeSpec_isPushout :
  ∀ {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
    (S : SurjectiveRingPullbackSituation B A A'),
    IsPushout
      (Spec.map (CommRingCat.ofHom S.toA))
      (Spec.map (CommRingCat.ofHom S.fromAprime))
      (Spec.map (CommRingCat.ofHom S.bprimeToB))
      (Spec.map (CommRingCat.ofHom S.bprimeToAprime)))
