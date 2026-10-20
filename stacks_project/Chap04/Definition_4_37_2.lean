/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Split
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Definition 4.37.2: split categories fibred in groupoids are represented by the conjunction of
the intrinsic split-fibration and fibered-in-groupoids properties. -/
@[stacks 04TL]
#check (Functor.IsFibered.Split.InGroupoids p : Prop)

/- Definition 4.37.2: the strict groupoid-valued presheaf model supplied by the canonical
split-fibration owner. -/
@[stacks 04TL "strict groupoid-valued model characterization"]
#check (Functor.IsFibered.Split.InGroupoids.iff_existsPresheafModel p)

end CategoryTheory
