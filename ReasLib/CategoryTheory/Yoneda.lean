/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

universe v u

namespace CategoryTheory

namespace Yoneda

variable {C : Type u} [Category.{v} C]

/-- Postcomposition by a morphism induces a bijection between morphisms and
natural transformations of the corresponding representable presheaves. -/
theorem map_bijective (X Y : C) :
    Function.Bijective (yoneda.map : (X ⟶ Y) → (yoneda.obj X ⟶ yoneda.obj Y)) := sorry

/-- The Yoneda presheaf evaluates at `U` as `U ⟶ X`, and restriction along
`φ : V ⟶ U` sends `ψ : U ⟶ X` to `φ ≫ ψ`. -/
theorem obj_spec (X : C) :
    (∀ U : C, (yoneda.obj X).obj (Opposite.op U) = (U ⟶ X)) ∧
      (∀ {U V : C} (φ : V ⟶ U) (ψ : U ⟶ X),
        (yoneda.obj X).map φ.op ψ = φ ≫ ψ) := sorry

end Yoneda

end CategoryTheory
