/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.61.5: a scheme morphism is flat and perfect if and only if it is flat and
locally of finite presentation. -/
@[stacks 068A] #check
  (AlgebraicGeometry.flat_and_perfect_iff_flat_and_locallyOfFinitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      (AlgebraicGeometry.Flat f ∧
          AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f) ↔
        (AlgebraicGeometry.Flat f ∧ AlgebraicGeometry.LocallyOfFinitePresentation f))
