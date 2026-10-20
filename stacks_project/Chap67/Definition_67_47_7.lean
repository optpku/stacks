/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Birational
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X Y : AlgebraicSpace S)
variable [AlgebraicSpace.IsIrreducible X] [AlgebraicSpace.IsIrreducible Y]

/- Definition 67.47.7: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`
with `|X|` and `|Y|` irreducible. We say `X` and `Y` are birational if they are isomorphic
in the category of irreducible algebraic spaces over `S` and dominant rational maps. -/
@[stacks 0EMT] #check (AlgebraicGeometry.AlgebraicSpace.Birational X Y : Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PartialIso :
  {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S → Type (u + 1))
