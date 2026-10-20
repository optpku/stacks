/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.InSets.LocalDiscreteness
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable (X Y : FiberedCategoryOver.Sets.{u, v, max w u, v} C)

/- Lemma 4.38.6 (1): every hom-category of categories fibred in sets is discrete. -/
@[stacks 02Y2 "(1)"]
#check (FiberedCategoryOver.Sets.homIsDiscrete X Y : IsDiscrete (X ⟶ Y))

/- Lemma 4.38.6 (2): the discrete Grothendieck construction is an equivalence from set-valued
presheaves to categories fibred in sets. -/
@[stacks 02Y2 "(2)"]
#check (FiberedCategoryOver.Sets.ofPresheaf.isEquivalence (C := C) :
  (FiberedCategoryOver.Sets.ofPresheaf C :
    (Cᵒᵖ ⥤ Type (max w u)) ⥤
      FiberedCategoryOver.Sets.{u, v, max w u, v} C).IsEquivalence)

end CategoryTheory
