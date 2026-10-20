/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 66.16.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
étale if and only if for every étale morphism `φ : U ⟶ X` from a scheme `U`, the
composition `φ ≫ f` is étale also. -/
@[stacks 03FR] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
      (X ⟶ Y) → Prop)
