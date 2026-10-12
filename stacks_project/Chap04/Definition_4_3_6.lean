/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (F : Cᵒᵖ ⥤ Type v)

/- Definition 4.3.6: representability of a presheaf is the canonical mathlib predicate
`CategoryTheory.Functor.IsRepresentable`: a contravariant functor `F : Cᵒᵖ ⥤ Type v` is
representable when it is isomorphic to `yoneda.obj U` for some object `U : C`. -/
@[stacks 001Q "representable presheaves as functors isomorphic to a Yoneda object"]
#check (Functor.IsRepresentable F : Prop)

end CategoryTheory
