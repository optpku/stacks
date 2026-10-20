/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCheckRecall

universe u

/- Lemma 29.25.10: A flat morphism locally of finite presentation is universally open. -/
@[stacks 01UA] #check
  (AlgebraicGeometry.UniversallyOpen.of_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f],
      AlgebraicGeometry.UniversallyOpen f)
