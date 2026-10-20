/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total

/-! # Derived tensor and sheaf internal Hom -/

public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived.Tensor

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (O : Sheaf J CommRingCat.{u})

private abbrev model (K : RingedSiteDerived J O) :=
  SheafOfModules.CellReplacement.model
    ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
      RingedSiteDerived J O).objPreimage K)

private theorem model_flat (K : RingedSiteDerived J O) : (model O K).IsKFlat :=
  SheafOfModules.RingedSite.CellReplacement.model_isKFlat _

private def flatModelIso (K : RingedSiteDerived J O) :
    DerivedCategory.Q.obj (model O K) ≅ K :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (SheafOfModules.CellReplacement.augmentation _))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (SheafOfModules.CellReplacement.augmentation_quasiIso _)) ≪≫
    (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
      RingedSiteDerived J O).objObjPreimageIso K

private theorem pairs_reach
    (P : ModuleHomotopy.{u} (RingedSite.ofCommRingSheaf J O) ×
      ModuleHomotopy.{u} (RingedSite.ofCommRingSheaf J O)) :
    ∃ P', ∃ s : P' ⟶ P, (P'.1.IsKFlat ∧ P'.2.IsKFlat) ∧ qis O s := by
  obtain ⟨r⟩ := (SheafOfModules.RingedSite.KFlat.hasResolutions (O := O)) P.1
  obtain ⟨s⟩ := (SheafOfModules.RingedSite.KFlat.hasResolutions (O := O)) P.2
  exact ⟨(r.X₁.obj, s.X₁.obj), (r.w, s.w), ⟨r.X₁.property, s.X₁.property⟩,
    r.hw, s.hw⟩

private theorem pairs_invert
    {P P' : ModuleHomotopy.{u} (RingedSite.ofCommRingSheaf J O) ×
      ModuleHomotopy.{u} (RingedSite.ofCommRingSheaf J O)}
    (f : P ⟶ P') (hP : P.1.IsKFlat ∧ P.2.IsKFlat)
    (hP' : P'.1.IsKFlat ∧ P'.2.IsKFlat) (hf : qis O f) :
    IsIso ((sourceFunctor O).map f) := by
  have hmon := HomotopyCategory.KFlat.quasiIsoIsMonoidal
    (C := ringedSiteModuleCategory J O)
  have ht := @MorphismProperty.tensorHom_mem _ _
    (HomotopyCategory.KFlat.quasiIso (C := ringedSiteModuleCategory J O)) _ hmon
    ⟨P.1, hP.1⟩ ⟨P'.1, hP'.1⟩ (ObjectProperty.homMk f.1)
    ⟨P.2, hP.2⟩ ⟨P'.2, hP'.2⟩ (ObjectProperty.homMk f.2) hf.1 hf.2
  exact (NatIso.isIso_map_iff
    (DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso
      (C := ringedSiteModuleCategory J O)) f).mp
    (Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (up ℤ)) _ ht)

private theorem pairs_compute
    (X Y : ModuleHomotopy.{u} (RingedSite.ofCommRingSheaf J O))
    (hX : X.IsKFlat) (hY : Y.IsKFlat) :
    Functor.LeftDerived.ComputesAt (sourceFunctor O) (qis O) (X, Y) :=
  Functor.LeftDerived.ComputesAt.of_mem_subset (sourceFunctor O) (qis O)
    (fun P ↦ P.1.IsKFlat ∧ P.2.IsKFlat) (pairs_reach O) (pairs_invert O) ⟨hX, hY⟩

private theorem hasPointwiseTensor :
    (sourceFunctor O).HasPointwiseLeftDerivedFunctor (qis O) :=
  Functor.LeftDerived.EverywhereDefined.hasPointwise_of_subset (sourceFunctor O) (qis O)
    (fun P ↦ P.1.IsKFlat ∧ P.2.IsKFlat) (pairs_reach O) (pairs_invert O)

private def tensorModelIso (K L : RingedSiteDerived J O) :
    obj O K L ≅ DerivedCategory.Q.obj (model O K ⊗ model O L) := by
  let P := ((HomotopyCategory.quotient _ (up ℤ)).obj (model O K),
    (HomotopyCategory.quotient _ (up ℤ)).obj (model O L))
  let e : (functor O).obj ((localization O).obj P) ≅ (sourceFunctor O).obj P :=
    @Functor.LeftDerived.ComputesAt.counitIso _ _ _ _ _ _
      (sourceFunctor O) (qis O) inferInstance (localization O) inferInstance
      (hasPointwiseTensor O) P
      (pairs_compute O P.1 P.2 (model_flat O K) (model_flat O L))
  exact (functor O).mapIso
      ((Iso.prod
        ((DerivedCategory.quotientCompQhIso _).app (model O K) ≪≫ flatModelIso O K)
        ((DerivedCategory.quotientCompQhIso _).app (model O L) ≪≫ flatModelIso O L)).symm) ≪≫
    e ≪≫
    DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorObjIso (model O K) (model O L)

@[implicit_reducible] private def strictClosed :
    MonoidalClosed (CochainComplex (ringedSiteModuleCategory J O) ℤ) :=
  CochainComplex.InternalHom.monoidalClosed

private def homModelIso (L M : RingedSiteDerived J O) :
    InternalHom.obj L M ≅
      DerivedCategory.Q.obj
        (CochainComplex.InternalHom.obj (model O L) (InternalHom.injectiveModel M)) := by
  let f := SheafOfModules.CellReplacement.augmentation
    ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
      RingedSiteDerived J O).objPreimage L)
  have hq := @SheafOfModules.RingedSite.IHom.quasiIso_map
    _ inferInstance J inferInstance inferInstance inferInstance O _ (strictClosed O)
    _ _ _ _ inferInstance inferInstance f (𝟙 (InternalHom.injectiveModel M))
    (SheafOfModules.CellReplacement.augmentation_quasiIso _)
    (inferInstance : QuasiIso (𝟙 (InternalHom.injectiveModel M)))
  unfold MonoidalClosed.Source.map at hq
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hq
  exact @asIso _ _ _ _
    (DerivedCategory.Q.map
      ((InternalHom.strictInternalHom.map f.op).app (InternalHom.injectiveModel M)))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq)

private def liftToInjective
    (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (hI : I.IsKInjective)
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj I) : F ⟶ I :=
  (HomotopyCategory.quotient _ (up ℤ)).preimage
    ((Equiv.ofBijective DerivedCategory.Qh.map
      (@CochainComplex.IsKInjective.Qh_map_bijective _ _ _ _
        ((HomotopyCategory.quotient _ (up ℤ)).obj F) I hI)).symm
      ((DerivedCategory.quotientCompQhIso _).hom.app F ≫ f ≫
        (DerivedCategory.quotientCompQhIso _).inv.app I))

/-- Currying a derived tensor morphism gives a morphism into derived sheaf internal Hom. -/
def curry (K L M : RingedSiteDerived J O) (f : obj O K L ⟶ M) :
    K ⟶ InternalHom.obj L M :=
  (flatModelIso O K).inv ≫
    DerivedCategory.Q.map
      (CochainComplex.InternalHom.curry
        ((β_ (model O L) (model O K)).hom ≫
          InternalHom.liftToInjectiveModel _ M ((tensorModelIso O K L).inv ≫ f))) ≫
    (homModelIso O L M).inv

/-- Uncurrying a morphism into derived sheaf internal Hom gives a derived tensor morphism. -/
def uncurry (K L M : RingedSiteDerived J O) (f : K ⟶ InternalHom.obj L M) :
    obj O K L ⟶ M := by
  have hI := @SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat
    _ inferInstance J inferInstance inferInstance inferInstance O _ (strictClosed O)
    _ _ (model O L) (InternalHom.injectiveModel M)
    (SheafOfModules.RingedSite.CellReplacement.model_isKFlat _) inferInstance
  exact (tensorModelIso O K L).hom ≫
    DerivedCategory.Q.map
      ((β_ (model O K) (model O L)).hom ≫
        CochainComplex.InternalHom.uncurry
          (liftToInjective O (model O K)
            (CochainComplex.InternalHom.obj (model O L) (InternalHom.injectiveModel M))
            hI ((flatModelIso O K).hom ≫ f ≫ (homModelIso O L M).hom))) ≫
    (InternalHom.injectiveModelIso M).hom

/-- Currying after uncurrying recovers the morphism into derived sheaf internal Hom. -/
theorem curry_uncurry (K L M : RingedSiteDerived J O)
    (f : K ⟶ InternalHom.obj L M) :
    curry O K L M (uncurry O K L M f) = f := sorry

/-- Uncurrying after currying recovers the derived tensor morphism. -/
theorem uncurry_curry (K L M : RingedSiteDerived J O) (f : obj O K L ⟶ M) :
    uncurry O K L M (curry O K L M f) = f := sorry

/-- Derived sheaf internal Hom represents morphisms out of the derived tensor product. -/
@[expose]
def homEquiv (K L M : RingedSiteDerived J O) :
    (K ⟶ InternalHom.obj L M) ≃ (obj O K L ⟶ M) where
  toFun := uncurry O K L M
  invFun := curry O K L M
  left_inv := curry_uncurry O K L M
  right_inv := uncurry_curry O K L M

end RingedSite.Hom.ModuleDerived.Tensor
