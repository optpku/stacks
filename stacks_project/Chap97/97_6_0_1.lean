/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- 97.6.0.1: for a 1-morphism `p : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf`, a solution `(x', β, γ')` to an infinitesimal lifting
problem makes the square with top arrow `γ'|_U = restrictHom p i γ'`, left
arrow `p(β) = β.hom ▷ p`, bottom arrow `γ`, and right arrow the identity on
`y'|_U = slice.pullback i y'` commute. -/
@[stacks 06D0] #check (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.restrictionSquare :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    {U U' : Over S} (i : U ⟶ U') {x' : GroupoidsOver.slice U' ⟶ X}
    {y' : GroupoidsOver.slice U' ⟶ Y} {x : GroupoidsOver.slice U ⟶ X}
    (β : slice.pullback i x' ≅ x) (γ : x ≫ p ≅ slice.pullback i y')
    (γ' : x' ≫ p ≅ y'), Prop)
