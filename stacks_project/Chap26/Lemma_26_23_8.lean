/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]

/- Lemma 26.23.8 (1): an immersion of schemes is a monomorphism. -/
@[stacks 01L7] #check (inferInstance : Mono f)

/- Lemma 26.23.8 (2): an immersion of schemes is separated. -/
@[stacks 01L7] #check (inferInstance : IsSeparated f)
