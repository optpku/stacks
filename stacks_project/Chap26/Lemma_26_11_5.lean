/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

/- Lemma 26.11.5: intersecting affine neighbourhoods contain a common standard-open
neighbourhood. -/
@[stacks 01IW] #check AlgebraicGeometry.exists_basicOpen_le_affine_inter
