/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X)

/- 96.18.0.1: a 1-morphism f : 𝒰 ⟶ 𝒳 of categories fibred in groupoids over
(Sch/S)_fppf, drawn as the commuting triangle with projections q = 𝒰.p and
p = 𝒳.p. The Lean 1-cell is f : U ⟶ X in GroupoidsOver S, and the triangle
equation is toFunctor f ⋙ X.p = U.p. Informally 𝒰 is thought of as a covering
of 𝒳. -/
@[stacks 06X4] #check (CategoryTheory.FiberedCategoryOver.Groupoids.comm f : CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor f ⋙ X.p = U.p)

#check (f : U ⟶ X)
#check U.p
#check X.p
