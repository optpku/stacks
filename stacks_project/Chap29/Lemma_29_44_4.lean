/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 29.44.4: a morphism is finite exactly when it is integral and locally of finite
type. -/
@[stacks 01WJ] #check
  (AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.IsFinite f ↔
        AlgebraicGeometry.IsIntegralHom f ∧ AlgebraicGeometry.LocallyOfFiniteType f)
