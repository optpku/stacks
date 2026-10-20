module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of fixed-right derived tensor objects in both variables

The fixed-right derived tensor `DerivedTensor.Right.obj K L` is functorial in `K` by
construction.  Functoriality in both variables is obtained by transporting the two-variable
derived tensor bifunctor along the canonical fixed-right comparison `Bifunctor.Right.isoApp`.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Right

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [Bifunctor.Has (C := C)] [DerivedTensor.Right.Has (C := C)]

/-- The map `f ⊗ᴸ g : K ⊗ᴸ L ⟶ K' ⊗ᴸ L'` of fixed-right derived tensor objects induced by maps in
both variables: the two-variable derived tensor map transported along the canonical fixed-right
comparisons. -/
@[stacks 064M "fixed-right derived tensor map in both variables"]
noncomputable def tensorHom
    {K K' L L' : DerivedCategory C} [Compatible L] [Compatible L']
    (f : K ⟶ K') (g : L ⟶ L') :
    DerivedTensor.Right.obj K L ⟶ DerivedTensor.Right.obj K' L' :=
  (isoApp L K).hom ≫ Bifunctor.functor.map (Prod.mkHom f g) ≫ (isoApp L' K').inv

/-- Defining equation of `tensorHom` through the two-variable derived tensor. -/
theorem tensorHom_def
    {K K' L L' : DerivedCategory C} [Compatible L] [Compatible L']
    (f : K ⟶ K') (g : L ⟶ L') :
    tensorHom f g =
      (isoApp L K).hom ≫ Bifunctor.functor.map (Prod.mkHom f g) ≫ (isoApp L' K').inv := sorry

/-- The tensor of two identities is the identity. -/
@[simp]
theorem tensorHom_id (K L : DerivedCategory C) [Compatible L] :
    tensorHom (𝟙 K) (𝟙 L) = 𝟙 (DerivedTensor.Right.obj K L) := sorry

/-- `tensorHom` is compatible with composition in both variables. -/
@[reassoc]
theorem tensorHom_comp
    {K K' K'' L L' L'' : DerivedCategory C} [Compatible L] [Compatible L'] [Compatible L'']
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    tensorHom (f ≫ f') (g ≫ g') = tensorHom f g ≫ tensorHom f' g' := sorry

/-- In the left variable, `tensorHom` is the map of the fixed-right derived tensor functor. -/
theorem tensorHom_id_right {K K' : DerivedCategory C} (L : DerivedCategory C) [Compatible L]
    (f : K ⟶ K') :
    tensorHom f (𝟙 L) = (DerivedTensor.Right.functor L).map f := sorry

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Right
