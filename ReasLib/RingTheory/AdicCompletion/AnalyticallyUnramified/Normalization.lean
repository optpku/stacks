/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Normalization of Analytically Unramified Local Rings

This leaf records the finite-normalization and `N-1` consequences of
analytic unramifiedness.
-/

universe u

namespace IsAnalyticallyUnramified

/-- Lemma 10.162.10 (4), tag `032Y`: the integral closure of an analytically
unramified Noetherian local ring in its total quotient ring is finite. -/
@[stacks 032Y "(4)"]
theorem integralClosure_fractionRing_finite {R : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAnalyticallyUnramified R] :
    Module.Finite R (integralClosure R (FractionRing R)) := sorry

/-- Lemma 10.162.10 (5), tag `032Y`: an analytically unramified Noetherian
local domain is `N-1`. -/
@[stacks 032Y "(5)"]
theorem isN1Ring {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] [IsAnalyticallyUnramified R] :
    IsN1Ring R := sorry

end IsAnalyticallyUnramified
