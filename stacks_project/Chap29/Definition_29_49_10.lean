/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

variable (X Y : AlgebraicGeometry.Scheme.{u})
  [IrreducibleSpace X] [IrreducibleSpace Y]
variable (φ : X ⤏ Y)

/- Definition 29.49.10: A rational map between irreducible schemes is dominant when any
representative is a dominant morphism of schemes. -/
@[stacks 0A1Z] #check
  (AlgebraicGeometry.Scheme.RationalMap.IsDominant φ : Prop)

variable (f : X.PartialMap Y)

#check
  (AlgebraicGeometry.Scheme.PartialMap.isDominant_toRationalMap_iff f :
    f.toRationalMap.IsDominant ↔ AlgebraicGeometry.IsDominant f.hom)
