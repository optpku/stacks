module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory.DerivedCategory.DerivedTensor.Presentation

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [HasDerivedCategory.{w₁} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalPreadditive C]
  [∀ A B : GradedObject ℤ C, GradedObject.HasTensor A B]
  [∀ A B D : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor A B D]
variable [∀ A B D : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ A B D]
  [∀ A B D E : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt A B D E]
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := C)]
  [MonoidalCategory (DerivedCategory C)]

-- Concrete sheaf/cochain tensor specializations require definitional comparison of canonical
-- totalized and localized tensor presentations.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The comparison with ordinary totalized tensor, transported from the actual derived tensor
bifunctor, rather than from an unrelated monoidal structure. -/
def counit
    (T : tensor (DerivedCategory C) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor)
    (K L : CochainComplex C ℤ) :
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ⟶
      DerivedCategory.Q.obj (K ⊗ L) :=
  T.hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
    DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ K L

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasDerivedCategory.{w₂} D] [MonoidalCategory D] [SymmetricCategory D]
  [MonoidalPreadditive D]
  [∀ A B : GradedObject ℤ D, GradedObject.HasTensor A B]
  [∀ A B E : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor A B E]
variable [∀ A B E : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ A B E]
  [∀ A B E G : GradedObject ℤ D, GradedObject.HasTensor₄ObjExt A B E G]
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := D)]
  [MonoidalCategory (DerivedCategory D)]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.Monoidal] [Functor.Cochain.HasMappedTensorTotals F]
  [F.mapDerivedCategory.Monoidal]
  [∀ K L : CochainComplex C ℤ, IsIso (Functor.Cochain.tensorComparison F K L)]

-- Concrete sheaf/cochain tensor specializations require definitional comparison of canonical
-- totalized and localized tensor presentations.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Compatibility of inverse-image tensor maps with their canonical sheaf-level map and its
termwise derived construction. This excludes rescaling the tensorator independently of the
specified derived tensor presentations. -/
def Pullback
    (TC : tensor (DerivedCategory C) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor)
    (TD : tensor (DerivedCategory D) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor)
    (sheafTensor : ∀ A B : C, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B) : Prop :=
  (∀ A B : C, OplaxMonoidal.δ F A B = sheafTensor A B) ∧
  (∀ K L : CochainComplex C ℤ,
    F.mapDerivedCategory.map (counit TC K L) ≫
        F.mapDerivedCategoryFactors.hom.app (K ⊗ L) ≫
        DerivedCategory.Q.map (inv (Functor.Cochain.tensorComparison F K L)) =
      OplaxMonoidal.δ F.mapDerivedCategory
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        (F.mapDerivedCategoryFactors.hom.app K ⊗ₘ F.mapDerivedCategoryFactors.hom.app L) ≫
        counit TD
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))

variable {F}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
omit [SymmetricCategory C] [SymmetricCategory D] in
/-- A tensor-compatible inverse-image functor has the specified base-category tensor map. -/
theorem Pullback.sheaf_map
    {TC : tensor (DerivedCategory C) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor}
    {TD : tensor (DerivedCategory D) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor}
    {sheafTensor : ∀ A B : C, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B}
    (h : Pullback F TC TD sheafTensor) (A B : C) :
    OplaxMonoidal.δ F A B = sheafTensor A B :=
  h.1 A B

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
omit [SymmetricCategory C] [SymmetricCategory D] in
/-- The derived tensor map of a tensor-compatible inverse-image functor descends its ordinary
totalized tensor map. -/
theorem Pullback.derived_map
    {TC : tensor (DerivedCategory C) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor}
    {TD : tensor (DerivedCategory D) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor}
    {sheafTensor : ∀ A B : C, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B}
    (h : Pullback F TC TD sheafTensor) (K L : CochainComplex C ℤ) :
    F.mapDerivedCategory.map (counit TC K L) ≫
        F.mapDerivedCategoryFactors.hom.app (K ⊗ L) ≫
        DerivedCategory.Q.map (inv (Functor.Cochain.tensorComparison F K L)) =
      OplaxMonoidal.δ F.mapDerivedCategory
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        (F.mapDerivedCategoryFactors.hom.app K ⊗ₘ F.mapDerivedCategoryFactors.hom.app L) ≫
        counit TD
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  h.2 K L

variable (F)

-- Concrete sheaf/cochain tensor specializations require definitional comparison of canonical
-- totalized and localized tensor presentations.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Assemble the two normalization laws for a tensor-compatible inverse-image functor. -/
def Pullback.ofComparisons
    (TC : tensor (DerivedCategory C) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor)
    (TD : tensor (DerivedCategory D) ≅ DerivedCategory.DerivedTensor.Bifunctor.functor)
    (sheafTensor : ∀ A B : C, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (hs : ∀ A B : C, OplaxMonoidal.δ F A B = sheafTensor A B)
    (hd : ∀ K L : CochainComplex C ℤ,
      F.mapDerivedCategory.map (counit TC K L) ≫
          F.mapDerivedCategoryFactors.hom.app (K ⊗ L) ≫
          DerivedCategory.Q.map (inv (Functor.Cochain.tensorComparison F K L)) =
        OplaxMonoidal.δ F.mapDerivedCategory
            (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
          (F.mapDerivedCategoryFactors.hom.app K ⊗ₘ F.mapDerivedCategoryFactors.hom.app L) ≫
          counit TD
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    Pullback F TC TD sheafTensor := ⟨hs, hd⟩


end CategoryTheory.DerivedCategory.DerivedTensor.Presentation

end
