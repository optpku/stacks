/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Colimits
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

/- Lemma 78.12.5: the category of quasi-coherent modules on a groupoid in algebraic
spaces `(U, R, s, t, c)` over `B` has colimits. -/
@[stacks 077X] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.hasColimitsOfSize :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      HasColimitsOfSize.{u, u} G.QCoh)
