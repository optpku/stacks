/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
variable (i : T ⟶ T') [IsFirstOrderThickening i.left]
variable (f : X ⟶ Y) (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
variable (γ : overMap i ≫ y ≅ x ≫ f)
variable (x' : GroupoidsOver.slice T' ⟶ X)

/- 106.8.1.1: the solid 2-commutative square for a morphism `f : X ⟶ Y` of
algebraic stacks, with affine first-order thickening `i : T ⟶ T'`, points
`x : GroupoidsOver.slice T ⟶ X` and `y : GroupoidsOver.slice T' ⟶ Y`, and
witness `γ : overMap i ≫ y ≅ x ≫ f`. The canonical constructor is checked
first, followed by the concrete displayed square. -/
@[stacks 0DNX] #check (CategoryTheory.Bicategory.PseudoPullbackCone.mk :
  ∀ (y₀ : GroupoidsOver.slice T' ⟶ Y) (f₀ : X ⟶ Y) (P : GroupoidsOver S)
    (j : P ⟶ GroupoidsOver.slice T') (z : P ⟶ X),
    (j ≫ y₀ ≅ z ≫ f₀) → Bicategory.PseudoPullbackCone y₀ f₀)

#check (CategoryTheory.Bicategory.PseudoPullbackCone.mk y f
  (GroupoidsOver.slice T) (overMap i) x γ : Bicategory.PseudoPullbackCone y f)

/- Companion check: the displayed dotted diagonal has type
`GroupoidsOver.slice T' ⟶ X`. -/
#check (x' : GroupoidsOver.slice T' ⟶ X)
