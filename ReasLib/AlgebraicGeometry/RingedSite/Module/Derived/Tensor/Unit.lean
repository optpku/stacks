/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total

/-!
# The structure module as a unit for derived tensoring
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

private theorem unitQuasiIsoSystem (O : Sheaf J CommRingCat.{w}) :
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)).IsSaturatedMultiplicativeSystem where
  toHasLeftCalculusOfFractions := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  toHasRightCalculusOfFractions := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  toHasSaturationAxiom := inferInstance

private theorem unitTensor_inverts (O : Sheaf J CommRingCat.{w})
    (E : RingedSiteDerived J O)
    {X Y : HomotopyCategory (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)}
    (f : X ⟶ Y) (hX : X.IsKFlat) (hY : Y.IsKFlat)
    (hf : HomotopyCategory.quasiIso _ _ f) :
    IsIso ((@DerivedCategory.DerivedTensor.Left.sourceFunctor
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _
      (moduleCategoryHasMapBifunctor O) E).map f) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hfq : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp hf
  change IsIso ((@DerivedCategory.Qh (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map
    ((Functor.Homotopy.BifunctorTotal.leftFixed _ _).map
      ((HomotopyCategory.quotient _ _).map f)))
  rw [Functor.Homotopy.BifunctorTotal.leftFixed_map]
  change IsIso ((@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map (HomologicalComplex.tensorHom (𝟙 _) f))
  apply (@DerivedCategory.isIso_Q_map_iff_quasiIso
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ _).mpr
  exact @CochainComplex.IsKFlat.quasiIso_tensorHom_right
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX hY f hfq

/-- Tensoring a derived module complex with the structure module maps canonically to that
complex through the tensor-unit comparison. -/
def derivedTensorLeftUnitHom (K : RingedSiteDerived J O) :
    (derivedTensorLeft K).obj
      ((@DerivedCategory.singleFunctor
        (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
        (moduleCategoryHasDerivedCategory (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O)) ⟶ K := by
  let Q := @DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O))
  let Qh := @DerivedCategory.Qh (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O))
  let F := @DerivedCategory.DerivedTensor.Left.sourceFunctor
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) K
  let S := HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)
  let T := HomologicalComplex.tensorUnit (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)
  have hT : T.IsKFlat := by
    intro M hM hacyclic n
    exact (hacyclic n).of_iso (HomologicalComplex.rightUnitor M).symm
  have hcomp : Functor.LeftDerived.ComputesAt F S ((HomotopyCategory.quotient _ _).obj T) :=
    @Functor.LeftDerived.ComputesAt.of_fullSubcategory _ _ _ _ F S
      (by exact unitQuasiIsoSystem O) (HomotopyCategory.kFlat _)
      (KFlat.hasResolutions (O := O))
      (by intro X Y f hf; exact unitTensor_inverts O K f.hom X.property Y.property hf) _ hT
  have hdefined : Functor.LeftDerived.EverywhereDefined F S :=
    (moduleCategoryHasDerivedTensor O).left.everywhereDefined K
  let e := Functor.LeftDerived.ComputesAt.counitIso F S Qh
    ((HomotopyCategory.quotient _ _).obj T) hcomp
  let eunit := Q.mapIso ((HomologicalComplex.single _ (up ℤ) (0 : ℤ)).mapIso
    (unitIsoTensorUnit (J := J) (𝒪 := O)))
  exact ((derivedTensorLeft K).mapIso eunit ≪≫ e ≪≫
    Q.mapIso (HomologicalComplex.rightUnitor (Q.objPreimage K)) ≪≫ Q.objObjPreimageIso K).hom

/-- A derived module complex maps canonically to its derived tensor product with the
structure module. -/
def derivedTensorLeftUnitInv (K : RingedSiteDerived J O) :
    K ⟶ (derivedTensorLeft K).obj
      ((@DerivedCategory.singleFunctor
        (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
        (moduleCategoryHasDerivedCategory (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O)) := by
  let Q := @DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O))
  let Qh := @DerivedCategory.Qh (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O))
  let F := @DerivedCategory.DerivedTensor.Left.sourceFunctor
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) K
  let S := HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)
  let T := HomologicalComplex.tensorUnit (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)
  have hT : T.IsKFlat := by
    intro M hM hacyclic n
    exact (hacyclic n).of_iso (HomologicalComplex.rightUnitor M).symm
  have hcomp : Functor.LeftDerived.ComputesAt F S ((HomotopyCategory.quotient _ _).obj T) :=
    @Functor.LeftDerived.ComputesAt.of_fullSubcategory _ _ _ _ F S
      (by exact unitQuasiIsoSystem O) (HomotopyCategory.kFlat _)
      (KFlat.hasResolutions (O := O))
      (by intro X Y f hf; exact unitTensor_inverts O K f.hom X.property Y.property hf) _ hT
  have hdefined : Functor.LeftDerived.EverywhereDefined F S :=
    (moduleCategoryHasDerivedTensor O).left.everywhereDefined K
  let e := Functor.LeftDerived.ComputesAt.counitIso F S Qh
    ((HomotopyCategory.quotient _ _).obj T) hcomp
  let eunit := Q.mapIso ((HomologicalComplex.single _ (up ℤ) (0 : ℤ)).mapIso
    (unitIsoTensorUnit (J := J) (𝒪 := O)))
  exact ((derivedTensorLeft K).mapIso eunit ≪≫ e ≪≫
    Q.mapIso (HomologicalComplex.rightUnitor (Q.objPreimage K)) ≪≫ Q.objObjPreimageIso K).inv

/-- The forward tensor-unit comparison followed by the reverse comparison is the identity. -/
theorem derivedTensorLeftUnit_hom_inv_id (K : RingedSiteDerived J O) :
    derivedTensorLeftUnitHom K ≫ derivedTensorLeftUnitInv K = 𝟙 _ := sorry

/-- The reverse tensor-unit comparison followed by the forward comparison is the identity. -/
theorem derivedTensorLeftUnit_inv_hom_id (K : RingedSiteDerived J O) :
    derivedTensorLeftUnitInv K ≫ derivedTensorLeftUnitHom K = 𝟙 _ := sorry

/-- The derived tensor product with the structure module is canonically isomorphic to the
original derived module complex. -/
def derivedTensorLeftUnitIso (K : RingedSiteDerived J O) :
    (derivedTensorLeft K).obj
      ((@DerivedCategory.singleFunctor
        (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
        (moduleCategoryHasDerivedCategory (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O)) ≅ K where
  hom := derivedTensorLeftUnitHom K
  inv := derivedTensorLeftUnitInv K
  hom_inv_id := derivedTensorLeftUnit_hom_inv_id K
  inv_hom_id := derivedTensorLeftUnit_inv_hom_id K

end SheafOfModules.RingedSite
