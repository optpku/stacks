/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback

/-!
# Pullback comparisons for groupoid schemes

This module provides the source-facing compatibility API for the canonical comparison between
pairs of arrows with a common target and composable pairs of arrows in a groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits

universe u

#check (AlgebraicGeometry.GroupoidScheme.targetComparisonIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
    pullback G.t G.t ≅ pullback G.s G.t)

namespace AlgebraicGeometry.GroupoidScheme

/-- The square with composition, second projection, and the two source maps is cartesian. -/
theorem compSquareIsPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.c (pullback.snd G.s G.t) G.s G.s := compSndIsPullback G

/-- The defining square for the composable-pair pullback is cartesian. -/
theorem projectionSquareIsPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t :=
  fstSndIsPullback G

end AlgebraicGeometry.GroupoidScheme
