/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.ProperHypercovering

/-!
# Proper hypercoverings in `LCCat`

Proper hypercoverings use the degree-zero augmentation and all relative matching
maps in the slice over the augmentation target.
-/

@[expose] public section

universe u

open CategoryTheory

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)

#check (LCCat.IsProperHypercovering a : Prop)
