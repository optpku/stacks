/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Functor.IsFibered.InGroupoids

universe uA uB uC vA vB vC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
variable (F : A ⥤ B) (G : B ⥤ C)
variable [Functor.IsFibered.InGroupoids F] [Functor.IsFibered.InGroupoids G]

/- Lemma 4.35.14 (Stacks 09WW): the composite of two functors fibred in groupoids is fibred in
groupoids. The canonical reusable instance is
`Functor.IsFibered.InGroupoids.Comp.inGroupoids`. -/
@[stacks 09WW]
#check (Comp.inGroupoids F G : Functor.IsFibered.InGroupoids (F ⋙ G))

end CategoryTheory.Functor.IsFibered.InGroupoids
