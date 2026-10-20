/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Thickening
import StacksCheckRecall

/-!
# Thickenings of algebraic spaces versus thickenings of small étale ringed topoi

A morphism of algebraic spaces is a thickening if and only if the associated morphism of
small étale ringed topoi is a thickening of ringed topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 91.14.1: A morphism of algebraic spaces is a thickening if and only if its
associated morphism of small étale ringed topoi is a thickening. -/
@[stacks 0D16] #check
  (AlgebraicGeometry.AlgebraicSpace.isThickening_iff_ringedToposHom :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
      AlgebraicGeometry.AlgebraicSpace.IsThickening i ↔
        RingedSite.ToposHom.IsThickening (AlgebraicGeometry.AlgebraicSpace.ringedToposHom i))
