module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

/-- Structured-arrow objects are equivalent to pairs of an object and an arrow from `V`
to its image under `u`. -/
def objEquiv (V : D) (u : C ⥤ D) :
    StructuredArrow V u ≃ (Σ U : C, V ⟶ u.obj U) where
  toFun structuredArrow := ⟨structuredArrow.right, structuredArrow.hom⟩
  invFun objectPair := mk objectPair.2
  left_inv structuredArrow := obj_ext _ _ rfl (by simp)
  right_inv objectPair := by
    cases objectPair
    rfl

/-- The object equivalence sends a structured arrow to its right object and structure arrow. -/
@[simp]
theorem objEquiv_apply (V : D) (u : C ⥤ D) (structuredArrow : StructuredArrow V u) :
    objEquiv V u structuredArrow = ⟨structuredArrow.right, structuredArrow.hom⟩ := rfl

/-- The inverse object equivalence constructs the structured arrow from the supplied arrow. -/
@[simp]
theorem objEquiv_symm_apply (V : D) (u : C ⥤ D) (objectPair : Σ U : C, V ⟶ u.obj U) :
    (objEquiv V u).symm objectPair = mk objectPair.2 := rfl

end StructuredArrow

end CategoryTheory
