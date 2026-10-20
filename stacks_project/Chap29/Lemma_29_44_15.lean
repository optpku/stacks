/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/- Lemma 29.44.15: a finite monomorphism of schemes is a closed immersion. -/
@[stacks 03BB] #check
  ((AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono f).mpr :
    AlgebraicGeometry.IsFinite f ∧ CategoryTheory.Mono f →
      AlgebraicGeometry.IsClosedImmersion f)
