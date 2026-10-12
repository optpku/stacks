/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.External
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Model
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived colimit of an external tensor

This is the reusable module-presheaf form of the product-site lower-shriek comparison.  The
product tensor is the heterogeneous `DerivedTensor.External.obj`; the target tensor uses the
canonical derived tensor on `ModuleCat B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe q₁ q₂ q₁₂ u₁ v₁ u₂ v₂ w

namespace CategoryTheory.DerivedColimit.ExternalTensor

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {B : Type w} [CommRing B]

variable [HasColimitsOfShape C₁ᵒᵖ (ModuleCat.{w} B)]
variable [HasColimitsOfShape C₂ᵒᵖ (ModuleCat.{w} B)]
variable [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat.{w} B)]
variable [HasDerivedCategory.{q₁} (ModuleCat.Presheaf C₁ B)]
variable [HasDerivedCategory.{q₂} (ModuleCat.Presheaf C₂ B)]
variable [HasDerivedCategory.{q₁₂} (ModuleCat.Presheaf (C₁ × C₂) B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C₁ (ModuleCat.{w} B) :
    HomotopyCategory (ModuleCat.Presheaf C₁ B) (up ℤ) ⥤
      DerivedCategory (ModuleCat.{w} B))
  (HomotopyCategory.quasiIso (ModuleCat.Presheaf C₁ B) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C₂ (ModuleCat.{w} B) :
    HomotopyCategory (ModuleCat.Presheaf C₂ B) (up ℤ) ⥤
      DerivedCategory (ModuleCat.{w} B))
  (HomotopyCategory.quasiIso (ModuleCat.Presheaf C₂ B) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (C₁ × C₂) (ModuleCat.{w} B) :
    HomotopyCategory (ModuleCat.Presheaf (C₁ × C₂) B) (up ℤ) ⥤
      DerivedCategory (ModuleCat.{w} B))
  (HomotopyCategory.quasiIso (ModuleCat.Presheaf (C₁ × C₂) B) (up ℤ))]

/-- The source functor for the product-site lower-shriek comparison, formed by applying the
derived external tensor and then derived colimit over the product category. -/
@[stacks 08QB "derived colimit of the external tensor"]
noncomputable abbrev sourceFunctor :
    CategoryTheory.Functor
      (DerivedCategory (ModuleCat.Presheaf C₁ B) ×
        DerivedCategory (ModuleCat.Presheaf C₂ B))
      (DerivedCategory (ModuleCat B)) :=
  DerivedCategory.DerivedTensor.External.functor (C₁ := C₁) (C₂ := C₂) (B := B) ⋙
    categoryOverPointDerivedColimit (C₁ × C₂) (ModuleCat B)

/-- The target functor for the product-site lower-shriek comparison, formed by taking the two
derived colimits separately and then their canonical derived tensor. -/
@[stacks 08QB "tensor of the two derived colimits"]
noncomputable abbrev targetFunctor :
    CategoryTheory.Functor
      (DerivedCategory (ModuleCat.Presheaf C₁ B) ×
        DerivedCategory (ModuleCat.Presheaf C₂ B))
      (DerivedCategory (ModuleCat B)) :=
  (categoryOverPointDerivedColimit C₁ (ModuleCat B)).prod
      (categoryOverPointDerivedColimit C₂ (ModuleCat B)) ⋙
    DerivedCategory.DerivedTensor.Bifunctor.functor

/-- The comparison is natural in both derived presheaf variables. -/
@[stacks 08QB "natural derived external tensor comparison"]
theorem comparison_isomorphic : IsIsomorphic (sourceFunctor (C₁ := C₁) (C₂ := C₂) (B := B))
    (targetFunctor (C₁ := C₁) (C₂ := C₂) (B := B)) := sorry

/-- Lemma 21.39.9: for the projections `πᵢ : C₁ × C₂ ⥤ Cᵢ`, the derived lower shriek of the
derived external tensor of the two projection inverse images is isomorphic to the derived tensor
of the two lower shrieks in `DerivedCategory (ModuleCat B)`. -/
@[stacks 08QB]
theorem tensorProjectionInverseImages_isomorphic
    (K₁ : DerivedCategory (ModuleCat.Presheaf C₁ B))
    (K₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit (C₁ × C₂) (ModuleCat.{w} B)).obj
        (DerivedCategory.DerivedTensor.External.obj K₁ K₂))
      (DerivedCategory.DerivedTensor.Bifunctor.obj (C := ModuleCat.{w} B)
        ((categoryOverPointDerivedColimit C₁ (ModuleCat.{w} B)).obj K₁)
        ((categoryOverPointDerivedColimit C₂ (ModuleCat.{w} B)).obj K₂)) := sorry

/-- Product-site lower-shriek comparison with an explicit target tensor model.  The source keeps
the canonical external tensor, while `M` supplies the selected bifunctor on `DerivedCategory
 (ModuleCat B)` as reusable data. -/
@[stacks 08QB "derived external tensor comparison for an explicit target model"]
theorem tensorProjectionInverseImages_isomorphic_model
    (M : DerivedCategory.DerivedTensor.Bifunctor.Model (C := ModuleCat.{w} B))
    (K₁ : DerivedCategory (ModuleCat.Presheaf C₁ B))
    (K₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)) :
    IsIsomorphic
      ((categoryOverPointDerivedColimit (C₁ × C₂) (ModuleCat.{w} B)).obj
        (DerivedCategory.DerivedTensor.External.obj K₁ K₂))
      (M.obj
        ((categoryOverPointDerivedColimit C₁ (ModuleCat.{w} B)).obj K₁)
        ((categoryOverPointDerivedColimit C₂ (ModuleCat.{w} B)).obj K₂)) := sorry

end CategoryTheory.DerivedColimit.ExternalTensor
