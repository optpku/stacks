module

public import ReasLib.CategoryTheory.Presheaf.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

variable {C : Type u} [Category.{v} C] {F G : Presheaf C} (φ : F ⟶ G)

/-
Definition 7.3.1 (1): a map φ : F ⟶ G of Type-valued presheaves on a category C is injective if
for every object U of C the component φ.app (op U) : F.obj (op U) → G.obj (op U) is
Function.Injective.
-/
@[stacks 00V6 "(1)"]
#check (∀ U : C, Function.Injective (φ.app (op U)))

/-
Definition 7.3.1 (2): a map φ : F ⟶ G of Type-valued presheaves on a category C is surjective if
for every object U of C the component φ.app (op U) : F.obj (op U) → G.obj (op U) is
Function.Surjective.
-/
@[stacks 00V6 "(2)"]
#check (∀ U : C, Function.Surjective (φ.app (op U)))
