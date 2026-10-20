module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric

/-!
# Symmetric monoidal homotopy categories of cochain complexes

@stack 0FP8
@stack 0GWP

Homotopy equivalences are monoidal for the totalized tensor product.  Therefore the homotopy
category inherits its monoidal and symmetric structures from Mathlib's monoidal localization.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory.Koszul

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [HasBinaryBiproducts C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The quotient functor carries the tensor unit to the chosen tensor unit of the homotopy
category. -/
@[stacks 0FP8 "homotopy-category tensor unit"]
def quotientUnitIso :
    (HomotopyCategory.quotient C (up ℤ)).obj
        (MonoidalCategoryStruct.tensorUnit (CochainComplex C ℤ)) ≅
      (HomotopyCategory.quotient C (up ℤ)).obj
        (MonoidalCategoryStruct.tensorUnit (CochainComplex C ℤ)) :=
  Iso.refl _

/-- The proposition that homotopy equivalences of cochain complexes are stable under the
totalized tensor product. -/
@[stacks 0FP8 "tensor-descends condition"]
abbrev TensorDescends : Prop :=
  (HomologicalComplex.homotopyEquivalences C (up ℤ) :
    MorphismProperty (CochainComplex C ℤ)).IsMonoidal

/-- Homotopy equivalences of cochain complexes are closed under identities, composition, and
tensoring on either side. -/
@[stacks 0FP8 "homotopy equivalences are monoidal"]
theorem homotopyEquivalencesIsMonoidal : TensorDescends (C := C) := sorry

/-- The canonical tensor-descends fact supplies the localization instances for the homotopy
category. -/
@[stacks 0FP8 "canonical tensor-descends instance"]
instance tensorDescends : TensorDescends (C := C) := sorry

section Descends

variable [TensorDescends (C := C)]

/-- The monoidal structure on the homotopy category obtained by localizing the totalized tensor
product of cochain complexes. -/
@[stacks 0FP8 "homotopy-category monoidal structure",
  stacks 0GWP "monoidal structure", implicit_reducible]
noncomputable instance monoidalCategory :
    MonoidalCategory (HomotopyCategory C (up ℤ)) :=
  inferInstanceAs
    (MonoidalCategory
      (LocalizedMonoidal (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ) :
          MorphismProperty (CochainComplex C ℤ)) quotientUnitIso))

/-- The quotient from cochain complexes to their homotopy category is monoidal. -/
@[stacks 0GWP "monoidal quotient functor", implicit_reducible]
noncomputable instance quotientMonoidal :
    (HomotopyCategory.quotient C (up ℤ)).Monoidal :=
  inferInstanceAs
    ((Localization.Monoidal.toMonoidalCategory
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ)) quotientUnitIso).Monoidal)

/-- The symmetric structure on the homotopy category induced by the Koszul symmetry on cochain
complexes. -/
@[stacks 0FP8 "homotopy-category symmetric structure",
  stacks 0GWP "symmetric structure", implicit_reducible]
noncomputable instance symmetricCategory :
    SymmetricCategory (HomotopyCategory C (up ℤ)) :=
  inferInstanceAs
    (SymmetricCategory
      (LocalizedMonoidal (HomotopyCategory.quotient C (up ℤ))
        (HomologicalComplex.homotopyEquivalences C (up ℤ) :
          MorphismProperty (CochainComplex C ℤ)) quotientUnitIso))

end Descends

end CategoryTheory.HomotopyCategory.Koszul
