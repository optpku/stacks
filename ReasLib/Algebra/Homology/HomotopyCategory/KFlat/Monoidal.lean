module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# The monoidal category of K-flat complexes

K-flat objects form a full symmetric monoidal subcategory of the homotopy category.  This leaf
owns only the object property and its tensor closure; the restricted quasi-isomorphism system is
kept in a separate leaf so clients of K-flatness do not need homology or localization machinery.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [HasBinaryBiproducts C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

namespace KFlat

variable [Koszul.TensorDescends (C := C)]

/-- The K-flat object property contains the tensor unit and is closed under tensor products. -/
@[stacks 0FPB "K-flat objects are monoidal", instance]
theorem isMonoidal : (kFlat C).IsMonoidal := sorry

end KFlat

end CategoryTheory.HomotopyCategory
