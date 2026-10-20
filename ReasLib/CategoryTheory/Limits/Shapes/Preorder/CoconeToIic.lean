/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.Preorder.CoconeToIic.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Preorder.CoconeToIic.Computations

/-!
# Closed extensions of preorder diagrams by cocones

This umbrella exports the data and computation API for extending a functor on
`Set.Iio j` to `Set.Iic j` using a cocone point.
-/

@[expose] public section

open CategoryTheory Limits
