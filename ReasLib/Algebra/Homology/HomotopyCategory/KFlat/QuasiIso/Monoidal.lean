module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor compatibility of K-flat quasi-isomorphisms

@stack 0FPB

This leaf adds the monoidal denominator-system condition to restricted quasi-isomorphisms of
K-flat homotopy objects. Clients that only need K-flat resolutions can import the lighter
`KFlat.QuasiIso` leaf.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory.KFlat

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
variable [CategoryWithHomology C]
variable [Koszul.TensorDescends (C := C)]

/-- The proposition that restricted quasi-isomorphisms of K-flat objects are stable under the
tensor product. -/
@[stacks 0FPB "tensor-descends condition"]
abbrev TensorDescends : Prop := (quasiIso (C := C)).IsMonoidal

/-- Restricted quasi-isomorphisms of K-flat objects are stable under tensor products. This is not
installed as an instance while its placeholder proof could affect localized functor data. -/
@[stacks 0FPB "K-flat quasi-isomorphisms are monoidal"]
theorem quasiIsoIsMonoidal : TensorDescends (C := C) := sorry

end CategoryTheory.HomotopyCategory.KFlat
