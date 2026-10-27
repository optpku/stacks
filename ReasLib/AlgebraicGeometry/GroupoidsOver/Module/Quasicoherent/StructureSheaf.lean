/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Monoidal

/-! # Quasi-coherent structure modules and their multiplication -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory SheafOfModules.RingedSite
open scoped Bicategory

noncomputable section

-- The public module map uses private scalar and naturality proofs.
set_option backward.privateInPublic true
universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The quasi-coherent structure sheaf `O_X` of an algebraic stack, as the unit
module on the fppf ringed site. -/
theorem structureSheaf_isQuasicoherent (X : GroupoidsOver S) [AlgebraicStack X] :
    quasiCoherentModuleProperty X
      (SheafOfModules.unit (ringedSite X).structureSheaf) := sorry

/-- The quasi-coherent unit module on the fppf ringed site. -/
def structureSheaf (X : GroupoidsOver S) [AlgebraicStack X] : QCoh X where
  obj := SheafOfModules.unit (ringedSite X).structureSheaf
  property := structureSheaf_isQuasicoherent X

/-- The underlying module of `structureSheaf X` is the unit on the fppf ringed
site of `X`. -/
theorem structureSheaf_obj (X : GroupoidsOver S) [AlgebraicStack X] :
    (structureSheaf X).obj = SheafOfModules.unit (ringedSite X).structureSheaf :=
  rfl

/-- The coefficient map `O_X ⟶ f^{-1} O_Y` induces a morphism from the
quasi-coherent structure sheaf of `X` to the pullback of the structure sheaf of
`Y`. -/
def structureSheafPullbackHom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheaf X ⟶ (pullback f).obj (structureSheaf Y) :=
  homMk (SheafOfModules.unitToPushforwardObjUnit (structureSheafMap f))

/-- `structureSheafPullbackHom f` is `unitToPushforwardObjUnit` of
`structureSheafMap f`. -/
theorem structureSheafPullbackHom_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheafPullbackHom f =
      homMk (SheafOfModules.unitToPushforwardObjUnit (structureSheafMap f)) :=
  rfl

/-- Pullback of quasi-coherent structure sheaves along a 1-morphism is an
isomorphism, because `structureSheafMap` is an isomorphism. -/
instance structureSheafPullbackHom_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    IsIso (structureSheafPullbackHom f) :=
  sorry

/-- The additive coefficient isomorphism respects the module scalar actions. -/
private theorem structureSheafPullbackInv_module_smul {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : X.totalᵒᵖ) :
    let φ := (forget₂ RingCat.{u} AddCommGrpCat.{u}).map
      ((structureSheafIso f).hom.hom.app x)
    ∀ r, φ ≫ ((structureSheaf X).obj.val.obj x).smul r =
      (((pullback f).obj (structureSheaf Y)).obj.val.obj x).smul r ≫ φ := sorry

/-- The linear maps induced by the coefficient isomorphism commute with restriction. -/
private theorem structureSheafPullbackInv_module_naturality {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    let app := fun x : X.totalᵒᵖ ↦
      ModuleCat.homMk
        (M := ((pullback f).obj (structureSheaf Y)).obj.val.obj x)
        (N := (structureSheaf X).obj.val.obj x)
        ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
          ((structureSheafIso f).hom.hom.app x))
        (structureSheafPullbackInv_module_smul f x)
    ∀ ⦃x y : X.totalᵒᵖ⦄ (i : x ⟶ y),
      (((pullback f).obj (structureSheaf Y)).obj.val.map i) ≫
          (ModuleCat.restrictScalars
            ((AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj.map i).hom).map
            (app y) =
        app x ≫
          (structureSheaf X).obj.val.map i := sorry

/-- The inverse structure-module map has the additive components of the coefficient isomorphism. -/
def structureSheafPullbackInv_module {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ((pullback f).obj (structureSheaf Y)).obj ⟶ (structureSheaf X).obj where
  val.app x :=
    ModuleCat.homMk
      ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
        ((structureSheafIso f).hom.hom.app x))
      (structureSheafPullbackInv_module_smul f x)
  val.naturality := fun {x y} i ↦ structureSheafPullbackInv_module_naturality f i

/-- Inverse of `structureSheafPullbackHom`, as the quasi-coherent map associated
to `structureSheafIso`. -/
def structureSheafPullbackInv {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (pullback f).obj (structureSheaf Y) ⟶ structureSheaf X :=
  homMk (structureSheafPullbackInv_module f)

/-- The pullback of a quasi-coherent structure sheaf is canonically identified
with the structure sheaf of the source. -/
def structureSheafPullbackIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (pullback f).obj (structureSheaf Y) ≅ structureSheaf X where
  hom := structureSheafPullbackInv f
  inv := structureSheafPullbackHom f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `structureSheafPullbackInv f` is the quasi-coherent packaging of
`structureSheafPullbackInv_module f`. -/
theorem structureSheafPullbackInv_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    structureSheafPullbackInv f = homMk (structureSheafPullbackInv_module f) :=
  by rfl

/-- The forward map of `structureSheafPullbackIso` is the explicit structure
sheaf pullback map. -/
theorem structureSheafPullbackIso_hom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (structureSheafPullbackIso f).hom = structureSheafPullbackInv f :=
  rfl

/-- Comparison of the transported structure sheaf with the tensor unit of
commutative fppf modules. -/
def structureSheafCommUnitToTensorUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    (toCommFppfModules X).obj (structureSheaf X).obj ⟶ 𝟙_ (commAssociatedModules X .fppf) :=
  @unitModuleToTensorUnit.{u + 1, u, u} X.total inferInstance
    (X.associatedTopology .fppf)
    (associatedTopology_hasSheafCompose_commRing X .fppf)
    (associatedTopology_hasWeakSheafify X .fppf)
    (associatedTopology_wEqualsLocallyBijective X .fppf)
    (commAssociatedStructureSheaf X .fppf)

/-- Comparison of the tensor unit of commutative fppf modules with the
transported structure sheaf. -/
def tensorUnitToStructureSheafCommUnit (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟙_ (commAssociatedModules X .fppf) ⟶ (toCommFppfModules X).obj (structureSheaf X).obj :=
  @tensorUnitToUnitModule.{u + 1, u, u} X.total inferInstance
    (X.associatedTopology .fppf)
    (associatedTopology_hasSheafCompose_commRing X .fppf)
    (associatedTopology_hasWeakSheafify X .fppf)
    (associatedTopology_wEqualsLocallyBijective X .fppf)
    (commAssociatedStructureSheaf X .fppf)

/-- Recover a fppf module from its commutative presentation. -/
def fromToCommFppfModulesHom {X : GroupoidsOver S}
    (F : RingedSite.ModuleCat.{u} (ringedSite X)) :
    (fromCommFppfModules X).obj ((toCommFppfModules X).obj F) ⟶ F :=
  ⟨(PresheafOfModules.Restriction.compComponentIso'
        (associatedToCommStructurePresheafIso X .fppf).hom
        (associatedToCommStructurePresheafIso X .fppf).inv
        (𝟙 (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj)
        (Iso.hom_inv_id (associatedToCommStructurePresheafIso X .fppf)).symm F.val).hom ≫
      (PresheafOfModules.Restriction.idComponentIso'
        (𝟙 (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj) rfl F.val).hom⟩

/-- Multiplication of the quasi-coherent structure sheaf, obtained from the left
unitor of the commutative fppf tensor at the tensor unit. -/
def structureSheafMul (X : GroupoidsOver S) [AlgebraicStack X] :
    Fppf.tensor (structureSheaf X) (structureSheaf X) ⟶ structureSheaf X :=
  homMk
    ((fromCommFppfModules X).map
        (@moduleTensorMap.{u + 1, u, u} X.total inferInstance
            (X.associatedTopology .fppf)
            (associatedTopology_hasSheafCompose_commRing X .fppf)
            (associatedTopology_hasWeakSheafify X .fppf)
            (associatedTopology_wEqualsLocallyBijective X .fppf)
            (commAssociatedStructureSheaf X .fppf) _ _ _ _
            (structureSheafCommUnitToTensorUnit X)
            (structureSheafCommUnitToTensorUnit X) ≫
          (CategoryTheory.MonoidalCategory.leftUnitor
            (𝟙_ (commAssociatedModules X .fppf))).hom ≫
            tensorUnitToStructureSheafCommUnit X) ≫
      fromToCommFppfModulesHom (structureSheaf X).obj)

/-- `structureSheafMul X` is the transported left unitor of the commutative
fppf tensor at the unit. -/
theorem structureSheafMul_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    structureSheafMul X =
      homMk
        ((fromCommFppfModules X).map
            (@moduleTensorMap.{u + 1, u, u} X.total inferInstance
            (X.associatedTopology .fppf)
            (associatedTopology_hasSheafCompose_commRing X .fppf)
            (associatedTopology_hasWeakSheafify X .fppf)
            (associatedTopology_wEqualsLocallyBijective X .fppf)
            (commAssociatedStructureSheaf X .fppf) _ _ _ _
                (structureSheafCommUnitToTensorUnit X)
                (structureSheafCommUnitToTensorUnit X) ≫
              (CategoryTheory.MonoidalCategory.leftUnitor
            (𝟙_ (commAssociatedModules X .fppf))).hom ≫
                tensorUnitToStructureSheafCommUnit X) ≫
          fromToCommFppfModulesHom (structureSheaf X).obj) :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh

