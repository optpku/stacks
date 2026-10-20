/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.IsThickening :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
