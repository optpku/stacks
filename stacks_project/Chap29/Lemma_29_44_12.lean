/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

/- Lemma 29.44.12 (1): a closed immersion is finite. -/
@[stacks 035C] #check (@AlgebraicGeometry.IsFinite.instOfIsClosedImmersion :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeometry.IsFinite f)

/- Lemma 29.44.12 (2): a closed immersion is integral. -/
@[stacks 035C] #check (@AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeometry.IsIntegralHom f)
