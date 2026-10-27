/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-! # Fppf module direct image for algebraic stacks -/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Compatible sections of actual fppf type-valued sheaves along a morphism of
algebraic stacks are small in the coefficient universe. -/
instance hasSmallFppfTypeSections [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : HasSmallAssociatedTypeSections f StandardTopology.fppf := sorry

/-- Direct image of fppf modules along a morphism of algebraic stacks is additive. -/
instance instFppfModulePushforwardAdditive [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : (fppfModulePushforward f).Additive :=
  fppfModulePushforward_additive f

end AlgebraicGeometry.AlgebraicStack
