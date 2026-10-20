/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Preabelian
public import ReasLib.CategoryTheory.Filtration.Strict.CompositionCounterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.19.2 [0122] (1): filtered objects form a preadditive category with a zero object and
binary biproducts. -/
@[stacks 0122]
#check (inferInstance : Preadditive (FilteredObject C))
#check (inferInstance : HasZeroObject (FilteredObject C))
#check (inferInstance : HasBinaryBiproducts (FilteredObject C))

/- Lemma 12.19.2 [0122] (2): filtered objects have kernels and cokernels. -/
@[stacks 0122]
#check (inferInstance : HasKernels (FilteredObject C))
#check (inferInstance : HasCokernels (FilteredObject C))

/- Lemma 12.19.2 [0122] (3): filtered morphisms have canonical coimage and image objects, but
strict morphisms are not closed under composition in general. -/
@[stacks 0122]
#check (FilteredObject.Hom.coimage :
  ∀ {A B : FilteredObject C}, (A ⟶ B) → FilteredObject C)
#check (FilteredObject.Hom.image :
  ∀ {A B : FilteredObject C}, (A ⟶ B) → FilteredObject C)
#check FilteredObject.Hom.strict_comp_not_in_general

end CategoryTheory
