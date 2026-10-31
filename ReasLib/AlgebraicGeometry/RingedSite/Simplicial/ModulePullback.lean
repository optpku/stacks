/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Operators
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Comparison

/-!
# Module pullback comparisons for simplicial ringed sites
-/

-- Private comparison constructions supply the explicit public isomorphisms.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open Sheaf.InternalModule (underlyingApp)

noncomputable section

universe u v w uA vA

namespace RingedSite.Simplicial

/-- The underived comparison isomorphisms of a simplicial family of ringed topoi. -/
structure ModulePullbackFunctoriality
    (X : SimplexCategory → RingedSite.{u, v, w})
    [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint] where
  /-- Canonical identification `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*`. -/
  pullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom (ψ ≫ φ)).modulePullback ≅
      (fHom ψ).modulePullback ⋙ (fHom φ).modulePullback
  /-- Canonical identification `f_id^* ≅ 𝟭`. -/
  pullbackIdIso (n : SimplexCategory) :
    (fHom (𝟙 n)).modulePullback ≅
      𝟭 (SheafOfModules.{w} (X n).structureSheaf)

end RingedSite.Simplicial

namespace CategoryTheory.SimplicialSites

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Continuous pushforward has the identity cartesian product comparison. -/
private theorem continuousPushforward_mu
    {D E : Type u} [Category.{v} D] [Category.{v} E]
    (F : D ⥤ E) (JD : GrothendieckTopology D) (JE : GrothendieckTopology E)
    [F.IsContinuous JD JE]
    [(F.sheafPushforwardContinuous (Type w) JD JE).Monoidal]
    [PreservesFiniteProducts (F.sheafPushforwardContinuous (Type w) JD JE)]
    (P Q : Sheaf JE (Type w)) :
    Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous (Type w) JD JE) P Q = 𝟙 _ := by
  have h : CartesianMonoidalCategory.prodComparisonIso
      (F.sheafPushforwardContinuous (Type w) JD JE) P Q = Iso.refl _ := by
    ext <;> rfl
  exact (Functor.Monoidal.μ_of_cartesianMonoidalCategory
    (F.sheafPushforwardContinuous (Type w) JD JE) P Q).trans (congrArg Iso.inv h)

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]

variable [UnivLE.{max u v, w}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The direct image of a module uses the original addition on each section. -/
private theorem ringedModulePushforward_section_add {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules (componentRingedSite C J O n).structureSheaf)
    (U : (C.obj m)ᵒᵖ)
    (x y : M.val.obj ((C.map φ).toFunctor.op.obj U)) :
    (((ringedToposMap C J O φ).modulePushforward.obj M).val.obj U).isAddCommGroup.add x y =
      x + y := by
  let f := (C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
    (J m).toGrothendieck (J n).toGrothendieck
  letI : PreservesFiniteProducts f :=
    LeftExactAdjunction.pushforwardPreservesFiniteProducts (ringedToposMap C J O φ).toTopos
  letI := Functor.Monoidal.ofChosenFiniteProducts f
  change ((Functor.LaxMonoidal.μ f
    (Sheaf.InternalModule.ToInternal.carrier _ M)
    (Sheaf.InternalModule.ToInternal.carrier _ M) ≫
      f.map (Sheaf.InternalModule.ToInternal.add _ M)).hom.app U) (x, y) = _
  rw [continuousPushforward_mu]
  rfl

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Underlying type-valued sheaves identify the composite of module pushforwards along
`ringedToposMap ψ` and `ringedToposMap φ` with module pushforward along `ringedToposMap (ψ ≫ φ)`. -/
def ringedModulePushforwardCompUnderlyingIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).modulePushforward ⋙
        (ringedToposMap C J O ψ).modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O l).structureSheaf ≅
      (ringedToposMap C J O (ψ ≫ φ)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (componentRingedSite C J O l).structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ringedToposMap C J O φ).modulePushforward
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O ψ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ))
      (ringedToposMap C J O ψ).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf)
      (sheafPushforwardContinuousComp' (map_comp_toFunctor C ψ φ) (Type w)
        (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck) ≪≫
    (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O (ψ ≫ φ))).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem ringedModulePushforwardCompIso_add {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ∀ M U (x y : (((ringedToposMap C J O φ).modulePushforward ⋙ (ringedToposMap C J O ψ).modulePushforward).obj M).val.obj U),
      underlyingApp ((componentRingedSite C J O l).structureSheaf) ((ringedModulePushforwardCompUnderlyingIso C J O ψ φ).hom.app M) U (x + y) =
        underlyingApp ((componentRingedSite C J O l).structureSheaf) ((ringedModulePushforwardCompUnderlyingIso C J O ψ φ).hom.app M) U x +
          underlyingApp ((componentRingedSite C J O l).structureSheaf) ((ringedModulePushforwardCompUnderlyingIso C J O ψ φ).hom.app M) U y := by
  intro M U x y
  let t := ((map_comp_toFunctor C ψ φ).inv.app U.unop).op
  have hsource :=
    (ringedModulePushforward_section_add C J O ψ
      ((ringedToposMap C J O φ).modulePushforward.obj M) U x y).trans
    (ringedModulePushforward_section_add C J O φ M ((C.map ψ).toFunctor.op.obj U) x y)
  calc
    _ = M.val.map t ((M.val.obj
        ((C.map φ).toFunctor.op.obj ((C.map ψ).toFunctor.op.obj U))).isAddCommGroup.add x y) :=
      congrArg (fun z ↦ M.val.map t z) hsource
    _ = _ := (M.val.map t).hom.map_add' x y
    _ = _ := (ringedModulePushforward_section_add C J O (ψ ≫ φ) M U _ _).symm

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem ringedModulePushforwardCompIso_smul {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    ∀ M U (a : ((componentRingedSite C J O l).structureSheaf).obj.obj U) (x : (((ringedToposMap C J O φ).modulePushforward ⋙ (ringedToposMap C J O ψ).modulePushforward).obj M).val.obj U),
      underlyingApp ((componentRingedSite C J O l).structureSheaf) ((ringedModulePushforwardCompUnderlyingIso C J O ψ φ).hom.app M) U (a • x) =
        a • underlyingApp ((componentRingedSite C J O l).structureSheaf) ((ringedModulePushforwardCompUnderlyingIso C J O ψ φ).hom.app M) U x := sorry

/-- Module pushforwards along `ringedToposMap` compose as `f_{ψ ≫ φ,*}`. -/
def ringedModulePushforwardCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePushforward ⋙
      (ringedToposMap C J O ψ).modulePushforward ≅
      (ringedToposMap C J O (ψ ≫ φ)).modulePushforward :=
  Sheaf.InternalModule.functorIsoOfUnderlying _ (ringedModulePushforwardCompUnderlyingIso C J O ψ φ) (ringedModulePushforwardCompIso_add C J O ψ φ) (ringedModulePushforwardCompIso_smul C J O ψ φ)

/-- Underived module pullbacks along `ringedToposMap` compose as `f_{ψ ≫ φ}^*`. -/
def ringedModulePullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O (ψ ≫ φ)).modulePullback ≅
      (ringedToposMap C J O ψ).modulePullback ⋙
        (ringedToposMap C J O φ).modulePullback :=
  (Adjunction.leftAdjointCompIso
      (ringedToposMap C J O ψ).moduleAdjunction
      (ringedToposMap C J O φ).moduleAdjunction
      (ringedToposMap C J O (ψ ≫ φ)).moduleAdjunction
      (ringedModulePushforwardCompIso C J O ψ φ)).symm

/-- The functor `(C.map (𝟙 n)).toFunctor` is the identity on the stage category. -/
private def map_id_toFunctor (n : SimplexCategory) :
    (C.map (𝟙 n)).toFunctor ≅ 𝟭 (C.obj n) :=
  Cat.Hom.toNatIso (eqToIso (C.map_id n))

/-- Underlying type-valued sheaves identify module pushforward along `ringedToposMap (𝟙 n)`
with the identity. -/
def ringedModulePushforwardIdUnderlyingIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) ⋙
        Sheaf.InternalModule.ToInternal.underlying
          (componentRingedSite C J O n).structureSheaf :=
  ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O (𝟙 n)) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying
        (componentRingedSite C J O n).structureSheaf)
      (sheafPushforwardContinuousId' (map_id_toFunctor C n) (Type w)
        (J n).toGrothendieck) ≪≫
    (Functor.rightUnitor _).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem ringedModulePushforwardIdIso_add (n : SimplexCategory) :
    ∀ M U (x y : (((ringedToposMap C J O (𝟙 n)).modulePushforward).obj M).val.obj U),
      underlyingApp ((componentRingedSite C J O n).structureSheaf) ((ringedModulePushforwardIdUnderlyingIso C J O n).hom.app M) U (x + y) =
        underlyingApp ((componentRingedSite C J O n).structureSheaf) ((ringedModulePushforwardIdUnderlyingIso C J O n).hom.app M) U x +
          underlyingApp ((componentRingedSite C J O n).structureSheaf) ((ringedModulePushforwardIdUnderlyingIso C J O n).hom.app M) U y := by
  intro M U x y
  let e := Cat.Hom.toNatIso (eqToIso (C.map_id n))
  calc
    _ = M.val.map (e.inv.app U.unop).op
        ((M.val.obj ((C.map (𝟙 n)).toFunctor.op.obj U)).isAddCommGroup.add x y) :=
      congrArg (fun z ↦ M.val.map (e.inv.app U.unop).op z)
        (ringedModulePushforward_section_add C J O (𝟙 n) M U x y)
    _ = _ := (M.val.map (e.inv.app U.unop).op).hom.map_add' x y

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem ringedModulePushforwardIdIso_smul (n : SimplexCategory) :
    ∀ M U (a : ((componentRingedSite C J O n).structureSheaf).obj.obj U) (x : (((ringedToposMap C J O (𝟙 n)).modulePushforward).obj M).val.obj U),
      underlyingApp ((componentRingedSite C J O n).structureSheaf) ((ringedModulePushforwardIdUnderlyingIso C J O n).hom.app M) U (a • x) =
        a • underlyingApp ((componentRingedSite C J O n).structureSheaf) ((ringedModulePushforwardIdUnderlyingIso C J O n).hom.app M) U x := sorry

/-- Module pushforward along `ringedToposMap (𝟙 n)` is the identity. -/
def ringedModulePushforwardIdIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePushforward ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) :=
  Sheaf.InternalModule.functorIsoOfUnderlying _ (ringedModulePushforwardIdUnderlyingIso C J O n) (ringedModulePushforwardIdIso_add C J O n) (ringedModulePushforwardIdIso_smul C J O n)

/-- Underived module pullback along `ringedToposMap (𝟙 n)` is the identity. -/
def ringedModulePullbackIdIso (n : SimplexCategory) :
    (ringedToposMap C J O (𝟙 n)).modulePullback ≅
      𝟭 (SheafOfModules.{w} (componentRingedSite C J O n).structureSheaf) :=
  Adjunction.leftAdjointIdIso
    (ringedToposMap C J O (𝟙 n)).moduleAdjunction
    (ringedModulePushforwardIdIso C J O n)

/-- Canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*` of derived module pullbacks. -/
def derivedPullbackCompComparison {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ringedToposMap C J O ψ).modulePullbackDerived ⋙
      (ringedToposMap C J O φ).modulePullbackDerived ⟶
      (ringedToposMap C J O (ψ ≫ φ)).modulePullbackDerived :=
  derivedPullbackCompComparisonOf
    (ringedToposMap C J O φ) (ringedToposMap C J O ψ) (ringedToposMap C J O (ψ ≫ φ))
    (ringedModulePullbackCompIso C J O ψ φ)

/-- Component of `derivedPullbackCompComparison` on an object of `D(O_l)`. -/
theorem derivedPullbackCompComparison_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : Hom.ModuleDerived.{w} (componentRingedSite C J O l)) :
    (derivedPullbackCompComparison C J O ψ φ).app K =
      (derivedPullbackCompComparisonOf
        (ringedToposMap C J O φ) (ringedToposMap C J O ψ)
        (ringedToposMap C J O (ψ ≫ φ)) (ringedModulePullbackCompIso C J O ψ φ)).app K :=
  rfl

/-- The composition comparison of derived module pullbacks is an isomorphism. -/
theorem derivedPullbackCompComparison_isIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    IsIso (derivedPullbackCompComparison C J O ψ φ) :=
  sorry

/-- Canonical comparison `id ⟶ Lf_id^*` of derived module pullbacks on a stage. -/
def derivedPullbackIdComparison (n : SimplexCategory) :
    𝟭 (Hom.ModuleDerived.{w} (componentRingedSite C J O n)) ⟶
      (ringedToposMap C J O (𝟙 n)).modulePullbackDerived :=
  derivedPullbackIdComparisonOf (ringedToposMap C J O (𝟙 n))
    (ringedModulePullbackIdIso C J O n)

/-- Component of `derivedPullbackIdComparison` on an object of `D(O_n)`. -/
theorem derivedPullbackIdComparison_app (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (componentRingedSite C J O n)) :
    (derivedPullbackIdComparison C J O n).app K =
      (derivedPullbackIdComparisonOf (ringedToposMap C J O (𝟙 n))
        (ringedModulePullbackIdIso C J O n)).app K :=
  rfl

/-- The identity comparison of derived module pullbacks is an isomorphism. -/
theorem derivedPullbackIdComparison_isIso (n : SimplexCategory) :
    IsIso (derivedPullbackIdComparison C J O n) := by
  apply (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (ringedToposMap C J O (𝟙 n)).modulePullbackDerived
      ((ToposHom.modulePullbackToDerived (ringedToposMap C J O (𝟙 n))).totalLeftDerivedCounit
        (Hom.moduleLocalization (componentRingedSite C J O n))
        (Hom.ModuleQis (componentRingedSite C J O n)))
      (Hom.ModuleQis (componentRingedSite C J O n)) _ _).mp
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (Functor.rightUnitor _ ≪≫
      (derivedPullbackIdSourceIsoOf (ringedToposMap C J O (𝟙 n))
        (ringedModulePullbackIdIso C J O n)).symm)

/-- The canonical module-pullback comparisons for the component ringed sites. -/
def modulePullbackFunctoriality :
    RingedSite.Simplicial.ModulePullbackFunctoriality
      (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) where
  pullbackCompIso := ringedModulePullbackCompIso C J O
  pullbackIdIso := ringedModulePullbackIdIso C J O

end CategoryTheory.SimplicialSites
