/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward

/-! # Fppf module direct image compatibility -/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Underived direct image of fppf modules along a morphism of algebraic stacks. -/
abbrev modulePushforward {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    fppfModules X ⥤ fppfModules Y :=
  fppfModulePushforward f

#check (modulePushforward :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → (fppfModules X ⥤ fppfModules Y))

end AlgebraicGeometry.AlgebraicStack
