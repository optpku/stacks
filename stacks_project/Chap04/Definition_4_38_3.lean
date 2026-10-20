/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
import StacksCheckRecall

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/- Definition 4.38.3 (1): an object of the `2`-category of categories fibred in sets over `C`
is a based category over `C` whose projection is fibred in sets. -/
@[stacks 04S8 "(1)"]
#check (FiberedCategoryOver.Sets.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Definition 4.38.3 (2): the `1`-morphisms are exactly the inherited homs in the direct full
subbicategory of `BasedCategory C`. -/
@[stacks 04S8 "(2)"]
#check (fun (X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C) ↦ (X ⟶ Y) :
  FiberedCategoryOver.Sets.{u, v, w, vS} C →
    FiberedCategoryOver.Sets.{u, v, w, vS} C → Type max w vS)

/- Definition 4.38.3 (3): the `2`-morphisms are the inherited morphisms in the relevant
hom-category. -/
@[stacks 04S8 "(3)"]
#check (fun {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    (F G : X ⟶ Y) ↦ (F ⟶ G) :
  {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C} →
    (F G : X ⟶ Y) → Type max w vS)

end CategoryTheory
