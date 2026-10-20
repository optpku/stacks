/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.RingTheory.Pullback.Spectrum

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace SurjectiveRingPullbackSituation

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- The affine spectra of a surjective ring pullback form a pushout square of schemes. -/
theorem schemeSpec_isPushout (S : SurjectiveRingPullbackSituation B A A') :
    IsPushout
      (Spec.map (CommRingCat.ofHom S.toA))
      (Spec.map (CommRingCat.ofHom S.fromAprime))
      (Spec.map (CommRingCat.ofHom S.bprimeToB))
      (Spec.map (CommRingCat.ofHom S.bprimeToAprime)) := sorry

end SurjectiveRingPullbackSituation
