/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback
import stacks_project.Chap78.Definition_78_11_1_Groupoid
import StacksCheckRecall

universe u

/- 79.3.0.1 (1): The lower-left square of the groupoid diagram is cartesian:
`pr₀` is `pullback.fst G.s G.t` and `pr₁` is `pullback.snd G.s G.t`. -/
@[stacks 04P9] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fstSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.IsPullback (CategoryTheory.Limits.pullback.fst G.s G.t)
        (CategoryTheory.Limits.pullback.snd G.s G.t) G.s G.t)

/- 79.3.0.1 (2): The lower-right square of composition and `pr₁` over `s` is cartesian. -/
@[stacks 04P9] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.compSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.IsPullback G.c (CategoryTheory.Limits.pullback.snd G.s G.t) G.s G.s)

/- 79.3.0.1 (3): The top square of `pr₀` and composition over `t` is cartesian. -/
@[stacks 04P9] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fstCompIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.IsPullback (CategoryTheory.Limits.pullback.fst G.s G.t) G.c G.t G.t)
