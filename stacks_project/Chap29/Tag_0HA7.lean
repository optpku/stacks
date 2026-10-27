/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition (0HA7) (1). A scheme is quasi-excellent if every point has an affine
open neighbourhood whose ring of sections is quasi-excellent. -/
@[stacks 0HA7] #check (AlgebraicGeometry.Scheme.QuasiExcellent : AlgebraicGeometry.Scheme.{u} → Prop)

/- Definition (0HA7) (2). A scheme is excellent if every point has an affine open
neighbourhood whose ring of sections is excellent. -/
@[stacks 0HA7] #check (AlgebraicGeometry.Scheme.Excellent : AlgebraicGeometry.Scheme.{u} → Prop)
