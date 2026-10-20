/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback
import StacksCheckRecall

open CategoryTheory Limits

universe u

/- 78.11.5.1: The map `(pr₀, c ∘ (i, 1))` identifies `pullback G.t G.t` with
`pullback G.s G.t`. Here pr₀ is `pullback.fst` and pr₁ is `pullback.snd`;
composition takes the later arrow first. The checks below record the forward map,
its projection and composition identities, and the two lower-left pullback squares. -/
@[stacks 04P3] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.Limits.pullback G.t G.t ≅ CategoryTheory.Limits.pullback G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso_hom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparisonIso.hom = G.targetComparison)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_fst :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_snd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ pullback.snd G.s G.t = G.leftDivision)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_cancel :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ G.c = pullback.snd G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.compSndIsPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    IsPullback G.c (pullback.snd G.s G.t) G.s G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.fstSndIsPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t)
