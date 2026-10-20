/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 29.41.1: a morphism of schemes is proper when it is separated, of finite type,
and universally closed. Universal closedness supplies quasi-compactness, so mathlib's
local-finite-type formulation is equivalent to the finite-type formulation here. -/
@[stacks 01W1] #check
  (AlgebraicGeometry.IsProper :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → Prop)

#check
  (AlgebraicGeometry.isProper_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsProper f ↔
        AlgebraicGeometry.IsSeparated f ∧
          AlgebraicGeometry.UniversallyClosed f ∧
            AlgebraicGeometry.LocallyOfFiniteType f)
