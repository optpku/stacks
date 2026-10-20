/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap109.Definition_109_22_2_Family
public import stacks_project.Chap109.Definition_109_22_2_Spaces
import StacksCheckRecall

@[expose] public section

/- Definition 109.22.2: a family of curves `f : X ⟶ S` is a stable family of
curves if it is prestable and, for every point `s` of `S`, the fibre `X_s`
has genus at least `2` and has neither a rational tail nor a rational bridge. -/
@[stacks 0E75] #check AlgebraicGeometry.AlgebraicSpace.IsStableFamily
