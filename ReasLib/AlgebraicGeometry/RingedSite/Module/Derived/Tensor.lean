/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left

/-!
# Derived tensor products of module sheaves on ringed sites

The ordinary tensor product on module sheaves is the canonical symmetric monoidal source for
derived tensoring.  This file owns the existence interface; downstream files use the generic
`DerivedTensor` construction and do not choose K-flat representatives or local instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The total tensor product of two unbounded complexes of module sheaves exists canonically. -/
@[stacks 06YU "complex tensor totalization", instance]
theorem moduleCategoryHasMapBifunctor
    (K L : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ringedSiteModuleCategory.{u, v, w, w} J O)) (up ℤ) := by
  intro n
  infer_instance

private theorem moduleQuasiIsoSystem :
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)).IsSaturatedMultiplicativeSystem where
  toHasLeftCalculusOfFractions := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  toHasRightCalculusOfFractions := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  toHasSaturationAxiom := inferInstance

private theorem leftTensor_inverts
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

private theorem rightTensor_inverts
    (E : RingedSiteDerived J O)
    {X Y : HomotopyCategory (ringedSiteModuleCategory.{u, v, w, w} J O) (up ℤ)}
    (f : X ⟶ Y) (hX : X.IsKFlat) (hY : Y.IsKFlat)
    (hf : HomotopyCategory.quasiIso _ _ f) :
    IsIso ((@DerivedCategory.DerivedTensor.Right.sourceFunctor
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _
      (moduleCategoryHasMapBifunctor O) E).map f) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hfq : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp hf
  let P := (@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).objPreimage E
  have ht : QuasiIso (HomologicalComplex.tensorHom (𝟙 P) f) :=
    @CochainComplex.IsKFlat.quasiIso_tensorHom_right
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P _ _ hX hY f hfq
  have : IsIso ((@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map (P ◁ f)) :=
    (@DerivedCategory.isIso_Q_map_iff_quasiIso
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ _).mpr inferInstance
  have h := congrArg (fun g => (@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map g)
    (HomologicalComplex.Koszul.braiding_natural_left (up ℤ) f P)
  simp only [Functor.map_comp] at h
  have : IsIso ((@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map (f ▷ P) ≫
      (@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map (HomologicalComplex.Koszul.braiding (up ℤ) Y P).hom) := by
    rw [h]
    infer_instance
  have hi : IsIso ((@DerivedCategory.Q (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map (f ▷ P)) :=
    (isIso_comp_right_iff _ _).mp this
  change IsIso ((@DerivedCategory.Qh (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O))).map
    ((Functor.Homotopy.BifunctorTotal.rightFixed _ _).map
      ((HomotopyCategory.quotient _ _).map f)))
  rw [Functor.Homotopy.BifunctorTotal.rightFixed_map]
  exact hi

/-- The canonical tensor product of module sheaves admits unbounded fixed-left and fixed-right
derived tensor functors. -/
@[stacks 06YU, instance]
theorem moduleCategoryHasDerivedTensor :
    @DerivedCategory.DerivedTensor.Has
      (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _
      (moduleCategoryHasMapBifunctor O) := by
  refine @DerivedCategory.DerivedTensor.Has.mk (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O)
    (@DerivedCategory.DerivedTensor.Right.Has.mk (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) ?_)
    (@DerivedCategory.DerivedTensor.Left.Has.mk (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) ?_)
  · intro E
    exact @Functor.LeftDerived.EverywhereDefined.of_fullSubcategory _ _ _ _
      (@DerivedCategory.DerivedTensor.Right.sourceFunctor (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) E)
      (HomotopyCategory.quasiIso _ (up ℤ)) (moduleQuasiIsoSystem O)
      (HomotopyCategory.kFlat _) (KFlat.hasResolutions (O := O))
      (fun X Y f hf => rightTensor_inverts O E f.hom X.property Y.property hf)
  · intro E
    exact @Functor.LeftDerived.EverywhereDefined.of_fullSubcategory _ _ _ _
      (@DerivedCategory.DerivedTensor.Left.sourceFunctor (ringedSiteModuleCategory.{u, v, w, w} J O) _ _ (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _ (moduleCategoryHasMapBifunctor O) E)
      (HomotopyCategory.quasiIso _ (up ℤ)) (moduleQuasiIsoSystem O)
      (HomotopyCategory.kFlat _) (KFlat.hasResolutions (O := O))
      (fun X Y f hf => leftTensor_inverts O E f.hom X.property Y.property hf)

variable {O}

/-- The canonical fixed-left derived tensor functor on derived module sheaves over a ringed
site. -/
def derivedTensorLeft (K : RingedSiteDerived J O) :
    RingedSiteDerived J O ⥤ RingedSiteDerived J O :=
  @DerivedCategory.DerivedTensor.Left.functor
    (ringedSiteModuleCategory.{u, v, w, w} J O) _ _
    (moduleCategoryHasDerivedCategory (𝒪 := O)) _ _
    (moduleCategoryHasMapBifunctor O) K (moduleCategoryHasDerivedTensor O).left

end

end SheafOfModules.RingedSite

