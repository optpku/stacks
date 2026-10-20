/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.BiproductLift
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasImages C] [HasPullbacks C]
  [HasBinaryBiproducts C]
variable {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D) [Mono f.hom]

/- Lemma 12.19.5 [05SK]: adjoining an arbitrary component to a strict monomorphism preserves
strictness. -/
@[stacks 05SK]
#check (strict_biprodLift f g : Strict f → Strict (biprod.lift f g))

end CategoryTheory.FilteredObject.Hom
