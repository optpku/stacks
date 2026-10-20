module

public import ReasLib.CategoryTheory.Presheaf.MonoEpi
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

variable {C : Type u} [Category.{v} C] {F G : Presheaf C} (φ : F ⟶ G)

/-
Definition 7.3.1 (1): a map φ : F ⟶ G of Type-valued presheaves on a category C is injective
exactly when it is monic, equivalently when every component φ.app (op U) is Function.Injective.
-/
@[stacks 00V6]
#check (CategoryTheory.Presheaf.mono_iff_injective φ :
  Mono φ ↔ ∀ U : C, Function.Injective (φ.app (op U)))

/-
Definition 7.3.1 (2): a map φ : F ⟶ G of Type-valued presheaves on a category C is surjective
exactly when it is epic, equivalently when every component φ.app (op U) is Function.Surjective.
-/
@[stacks 00V6 "(2)"]
#check (CategoryTheory.Presheaf.epi_iff_surjective φ :
  Epi φ ↔ ∀ U : C, Function.Surjective (φ.app (op U)))
