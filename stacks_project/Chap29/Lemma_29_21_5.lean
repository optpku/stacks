/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

/- Lemma 29.21.5: any open immersion is locally of finite presentation. -/
@[stacks 01TT] #check
  (AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f], LocallyOfFinitePresentation f)
