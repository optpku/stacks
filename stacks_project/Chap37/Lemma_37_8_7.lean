/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Unramified
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.8.7: An unramified flat morphism is formally étale. -/
@[stacks 04FF] #check
  (AlgebraicGeometry.Unramified.toFormallyEtale :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.FormallyEtale f)
