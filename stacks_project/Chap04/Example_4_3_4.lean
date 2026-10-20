/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
The scoped notation `h[U]` is a transparent view of the canonical owner `yoneda.obj U`. Unlike
`uliftYoneda`, it retains the source's literal hom-set values.
-/


open scoped RepresentablePresheaf

section

variable (U : C)

/- Example 4.3.4: the textbook representable presheaf attached to `U` is the canonical Yoneda
object `h[U] : Cᵒᵖ ⥤ Type v`. When `C` is a category of schemes, this presheaf is also called the
functor of points of `U`. -/
@[stacks 001O "representable presheaf associated to an object"]
#check (h[U] : Cᵒᵖ ⥤ Type v)

end

end CategoryTheory
