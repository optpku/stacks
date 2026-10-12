/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.«99_15_1_1_Curves»

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Spaces

/- 99.15.1.1: the category Curves of families of curves is a full subcategory
of Spaces'_{fp, flat, proper}. -/
@[stacks 0D50] #check CurvesGroupoids.inclusion
