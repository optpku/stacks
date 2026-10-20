/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import StacksCheckRecall

@[expose] public section


namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {S X Y P : C} (f : S ⟶ X) (g : S ⟶ Y) (p : X ⟶ P) (q : Y ⟶ P)
variable (h : IsPushout f g p q)

/- Mathlib's `IsPushout f g p q` is the source-facing owner: unlike the lower-level
`IsColimit (PushoutCocone.mk p q h)`, it packages the commutativity witness, and unlike
`Square.IsPushout`, it does not first bundle the diagram as a `Square`. This choice makes no
generalization: the source's object `x ⨿_y z` and maps `p`, `q` are the implicit codomain and
last two arguments. It also exposes `exists_desc` and `hom_ext` directly for downstream
universal-property arguments. -/

/-
Definition 4.9.1: a pushout of morphisms `f : y ⟶ x` and `g : y ⟶ z` is the canonical
mathlib notion `CategoryTheory.IsPushout f g p q`, consisting of an object `po` with
morphisms `p : x ⟶ po` and `q : z ⟶ po` forming a commutative square and satisfying the
stated universal property.
-/
@[stacks 0026 "pushout object with coprojections and universal mapping property"]
#check (IsPushout f g p q : Prop)

/- Companion recall: the commuting-square clause is the canonical projection
`IsPushout.toCommSq`. -/
#check h.toCommSq

/- Companion recall: the existence clause in the textbook universal property is the canonical
theorem `IsPushout.exists_desc`. -/
#check h.exists_desc

/- Companion recall: the uniqueness clause in the textbook universal property is the canonical
theorem `IsPushout.hom_ext`. -/
#check h.hom_ext

/- Companion recall: the converse direction from a colimiting pushout cocone is the canonical
constructor `IsPushout.of_isColimit`. -/
#check IsPushout.of_isColimit

end CategoryTheory
