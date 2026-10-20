/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Base

/-!
# Canonical base fibres of finite Hilbert stacks

The canonical fibre objects and their restriction comparisons over the big
fppf site of a scheme.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open FiberedCategoryOver.Groupoids

universe u

#check (AlgebraicGeometry.FiniteHilbertStack.baseFiber :
  ∀ {S : Scheme.{u}} (U : Over S), (schemeBase S).p.Fiber U)

#check (AlgebraicGeometry.FiniteHilbertStack.baseRestrictIso :
  ∀ {S : Scheme.{u}} {U Z : Over S} (π : Z ⟶ U),
    restrictObj (baseFiber U) π ≅ baseFiber Z)
