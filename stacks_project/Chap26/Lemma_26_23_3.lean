/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.23.3: a monomorphism of schemes is separated. -/
@[stacks 01L4] #check IsSeparated.isSeparated_of_mono
