/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

/-!
# Lemma 29.41.6

A closed immersion is proper, and hence universally closed.
-/

@[expose] public section

open CategoryTheory

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}}
variable (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f]

#check (AlgebraicGeometry.IsFinite.instOfIsClosedImmersion f :
  AlgebraicGeometry.IsFinite f)

/- Lemma 29.41.6: a closed immersion is proper. -/
@[stacks 01W5] #check (AlgebraicGeometry.IsProper.instOfIsFinite f :
  AlgebraicGeometry.IsProper f)

#check (AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion f :
  AlgebraicGeometry.UniversallyClosed f)
