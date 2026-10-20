/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f g : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K)

/- Definition 7.36.1: a 2-morphism from f to g is a transformation of
functors f.pushforward ⟶ g.pushforward. -/
@[stacks 04IA] #check
  (CategoryTheory.MorphismOfTopoiIn.TwoMorphism f g : Type (max u₁ u₂ v₂ (w + 1)))
