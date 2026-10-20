/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import StacksCheckRecall

@[expose] public section

universe u₁ u₂ v₁ v₂ w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Definition 7.43.1: for sites C and D, a morphism of topoi f : Sh(D) ⟶ Sh(C)
is an embedding exactly when the direct image f_* is fully faithful. This is
`MorphismOfTopoiIn.IsEmbedding`. -/
@[stacks 08LU] #check
  (CategoryTheory.MorphismOfTopoiIn.IsEmbedding :
    CategoryTheory.MorphismOfTopoiIn J K → Prop)
