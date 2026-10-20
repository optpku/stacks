/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Order
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (J J' : GrothendieckTopology C)

/- Definition 7.47.8: on a category C, a Grothendieck topology J is finer or stronger than J'
if and only if J' ≤ J, equivalently every covering sieve of J' is a covering sieve of J,
i.e. ∀ U, J' U ⊆ J U. In this case J' is coarser or weaker than J. -/
@[stacks 00Z6] #check (CategoryTheory.GrothendieckTopology.le_iff_forall_subset :
  J' ≤ J ↔ ∀ U : C, J' U ⊆ J U)

#check (CategoryTheory.GrothendieckTopology.instLEGrothendieckTopology :
  LE (GrothendieckTopology C))
#check (CategoryTheory.GrothendieckTopology.instPartialOrder :
  PartialOrder (GrothendieckTopology C))
#check (CategoryTheory.GrothendieckTopology.le_def :
  J' ≤ J ↔ ∀ U : C, J' U ⊆ J U)
