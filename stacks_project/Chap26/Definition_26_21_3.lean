/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.21.3 (1): separated morphisms. -/
@[stacks 01KK] #check IsSeparated

/- Definition 26.21.3 (2): quasi-separated morphisms. -/
@[stacks 01KK] #check QuasiSeparated

/- Definition 26.21.3 (3): separated schemes. -/
@[stacks 01KK] #check Scheme.IsSeparated

/- Definition 26.21.3 (4): quasi-separated schemes. -/
@[stacks 01KK] #check QuasiSeparatedSpace
