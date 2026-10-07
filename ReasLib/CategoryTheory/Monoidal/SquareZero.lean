module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Square-zero morphisms to the tensor unit

The square of `i : I ⟶ 𝟙_ C` is the canonical composite
`I ⊗ I ⟶ 𝟙_ C ⊗ I ⟶ I ⟶ 𝟙_ C`.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C]
variable [CategoryTheory.Limits.HasZeroMorphisms C] [MonoidalCategory C]

/-- The morphism `i : I ⟶ 𝟙_ C` is square-zero when multiplication through the tensor
unit vanishes on `I ⊗ I`. -/
@[stacks 08M4 "square-zero morphism"]
def IsSquareZero {I : C} (i : I ⟶ 𝟙_ C) : Prop :=
  (i ▷ I) ≫ (λ_ I).hom ≫ i = 0

/-- The defining composite for a square-zero morphism to the tensor unit. -/
theorem isSquareZero_iff {I : C} (i : I ⟶ 𝟙_ C) :
    IsSquareZero i ↔ (i ▷ I) ≫ (λ_ I).hom ≫ i = 0 := sorry

end CategoryTheory.MonoidalCategory
