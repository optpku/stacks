/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.CofilteredSystem
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory

/-
nLab identifies a directed preorder with a filtered `(0,1)`-category.  Dually, a directed inverse
system is a diagram on a cofiltered thin category, so the two source presentations are

- a general cofiltered system is a functor `F : J ⥤ Type`, with `J` cofiltered;
- a directed inverse system is a functor `F : Iᵒᵈ ⥤ Type`, with `I` directed.

The exact core owner is `nonempty_sections_of_finite_cofiltered_system`.  Its assumption
`IsCofilteredOrEmpty J` is slightly stronger than the source because it also admits the empty
index; the first tagged check deliberately retains `IsCofiltered J`.  Likewise, the inverse-system
check retains the chapter's `Nonempty J ∧ IsDirectedOrder J` presentation.

The specialized owner `nonempty_sections_of_finite_inverse_system` uses the categorical opposite
`Jᵒᵖ`, whereas Definition 4.21.4 consistently presents inverse systems on the order dual `Jᵒᵈ`.
Applying the general owner directly to `Jᵒᵈ` avoids transport along `orderDualEquivalence J`.
Finally, `F.sections.Nonempty` is mathlib's concrete compatible-family form of nonemptiness of the
`Type`-valued limit; a local limit wrapper would add no mathematical content.
-/

section Cofiltered

variable {J : Type u} [Category.{w} J] [IsCofiltered J]
variable (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)] [∀ j : J, Nonempty (F.obj j)]

/- Lemma 4.21.7 (1): the limit of a cofiltered diagram of finite nonempty sets is nonempty. -/
@[stacks 086J "nonempty limit of a cofiltered diagram of finite nonempty sets"]
#check (nonempty_sections_of_finite_cofiltered_system F : F.sections.Nonempty)

end Cofiltered

section InverseSystem

variable {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
variable (F : Jᵒᵈ ⥤ Type v) [∀ j : Jᵒᵈ, Finite (F.obj j)] [∀ j : Jᵒᵈ, Nonempty (F.obj j)]

/- Lemma 4.21.7 (2): equivalently, the inverse limit of a directed inverse system of finite nonempty
sets is nonempty. -/
@[stacks 086J "nonempty limit of a directed inverse system of finite nonempty sets"]
#check (nonempty_sections_of_finite_cofiltered_system F : F.sections.Nonempty)

end InverseSystem
