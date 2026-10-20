/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale.Unramified
import StacksCheckRecall

/-!
# Unramified flat morphisms of algebraic spaces are formally étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.16.7: An unramified flat morphism is formally étale. -/
@[stacks 0615] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.toFormallyEtale :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Unramified f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f],
      AlgebraicGeometry.AlgebraicSpace.FormallyEtale f)
