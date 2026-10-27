/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.StructureSheaf

/-! # Associated modules on affine scheme slices -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite
open scoped TensorProduct ChangeOfRings

noncomputable section

-- Public constructions retain private component formulas.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- Pullback of global sections along the structure morphism of a slice object. -/
def associatedSectionHom (U : Over S) (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    Γ(U.left, ⊤) →+* Γ(x.unop.left.left, ⊤) :=
  x.unop.hom.left.appTop.hom

private abbrev coefficients (U : Over S) (x : (GroupoidsOver.slice U).totalᵒᵖ) :=
  (ModuleCat.restrictScalars (associatedSectionHom U x)).obj
    (ModuleCat.of Γ(x.unop.left.left, ⊤) Γ(x.unop.left.left, ⊤))

/-- Scalar extension of a coordinate-ring module to a slice object's section ring. -/
def associatedExtend (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) : ModuleCat.{u} Γ(x.unop.left.left, ⊤) :=
  (ModuleCat.extendScalars (associatedSectionHom U x)).obj M

/-- The restriction homomorphism on section rings of slice objects. -/
def associatedRestrictRingHom (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    Γ(x.unop.left.left, ⊤) →+* Γ(y.unop.left.left, ⊤) :=
  f.unop.left.left.appTop.hom

/-- Restriction of coefficients respects the coordinate-ring scalar action. -/
theorem associatedRestrictLinear_laws (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    ∀ (a : Γ(U.left, ⊤)) (s : coefficients U x),
      associatedRestrictRingHom U f (a • s) =
        a • (show coefficients U y from associatedRestrictRingHom U f s) := sorry

/-- Restriction on section rings, linear over the coordinate ring. -/
def associatedRestrictLinear (U : Over S)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    coefficients U x →ₗ[Γ(U.left, ⊤)] coefficients U y where
  toFun := associatedRestrictRingHom U f
  map_add' := map_add _
  map_smul' := associatedRestrictLinear_laws U f

private def restrictionFunction (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    associatedExtend U M x → associatedExtend U M y :=
  TensorProduct.map (associatedRestrictLinear U f) (LinearMap.id (R := Γ(U.left, ⊤)))

/-- Tensor restriction is additive and semilinear over the restriction of sections. -/
theorem associatedPresheafMap_laws (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    (restrictionFunction U M f 0 = 0) ∧
    (∀ a b, restrictionFunction U M f (a + b) =
      restrictionFunction U M f a + restrictionFunction U M f b) ∧
    (∀ (r : Γ(x.unop.left.left, ⊤)) m,
      restrictionFunction U M f (r • m) =
        associatedRestrictRingHom U f r • restrictionFunction U M f m) := sorry

/-- The scalar-extension restriction map on associated modules. -/
def associatedPresheafMap (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    associatedExtend U M x ⟶
      (ModuleCat.restrictScalars
        ((GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.map f).hom).obj
        (associatedExtend U M y) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      { toFun := restrictionFunction U M f
        map_zero' := (associatedPresheafMap_laws U M f).1
        map_add' := (associatedPresheafMap_laws U M f).2.1 })
    (fun r ↦ by ext m; exact ((associatedPresheafMap_laws U M f).2.2 r m).symm)

/-- Associated restriction maps preserve identities and composition on sections. -/
theorem associatedPresheaf_laws (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    (∀ (x : (GroupoidsOver.slice U).totalᵒᵖ) (m : associatedExtend U M x),
      associatedPresheafMap U M (𝟙 x) m = m) ∧
    (∀ {x y z : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) (g : y ⟶ z)
      (m : associatedExtend U M x),
      associatedPresheafMap U M (f ≫ g) m =
        associatedPresheafMap U M g (associatedPresheafMap U M f m)) := sorry

/-- The module presheaf whose sections are scalar extensions of a coordinate-ring module. -/
def associatedPresheaf (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    PresheafOfModules.{u} (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj where
  obj x := associatedExtend U M x
  map f := associatedPresheafMap U M f
  map_id x := by ext m; exact (associatedPresheaf_laws U M).1 x m
  map_comp f g := by ext m; exact (associatedPresheaf_laws U M).2 f g m

/-- Associated presheaf sections are the specified scalar extensions. -/
theorem associatedPresheaf_obj (U : Over S) (M : ModuleCat.{u} Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    (associatedPresheaf U M).obj x = associatedExtend U M x := rfl

/-- Extension of a module map commutes with the associated restriction maps. -/
theorem associatedPresheafHom_naturality (U : Over S)
    {M N : ModuleCat.{u} Γ(U.left, ⊤)} (φ : M ⟶ N)
    {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y) :
    associatedPresheafMap U M f ≫
        (ModuleCat.restrictScalars
          ((GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.map f).hom).map
          ((ModuleCat.extendScalars (associatedSectionHom U y)).map φ) =
      (ModuleCat.extendScalars (associatedSectionHom U x)).map φ ≫
        associatedPresheafMap U N f := sorry

/-- The sectionwise scalar extension of a module morphism. -/
def associatedPresheafHom (U : Over S) {M N : ModuleCat.{u} Γ(U.left, ⊤)}
    (φ : M ⟶ N) : associatedPresheaf U M ⟶ associatedPresheaf U N where
  app x := (ModuleCat.extendScalars (associatedSectionHom U x)).map φ
  naturality := associatedPresheafHom_naturality U φ

/-- The associated presheaf morphisms preserve identities and composition. -/
theorem associatedModules_laws (U : Over S) :
    (∀ M : ModuleCat.{u} Γ(U.left, ⊤), associatedPresheafHom U (𝟙 M) = 𝟙 _) ∧
    (∀ {M N P : ModuleCat.{u} Γ(U.left, ⊤)} (f : M ⟶ N) (g : N ⟶ P),
      associatedPresheafHom U (f ≫ g) =
        associatedPresheafHom U f ≫ associatedPresheafHom U g) := sorry

/-- The scalar-extension presheaf functor on the big fppf slice of a scheme. -/
def associatedPresheaves (U : Over S) :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤
      PresheafOfModules.{u} (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj where
  obj M := associatedPresheaf U M
  map φ := associatedPresheafHom U φ
  map_id M := (associatedModules_laws U).1 M
  map_comp f g := (associatedModules_laws U).2 f g

/-- The associated module sheaf is the sheafification of the scalar-extension presheaf. -/
def associatedModules (U : Over S) [IsAffine U.left] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤
      RingedSite.ModuleCat.{u} (ringedSite (GroupoidsOver.slice U)) :=
  associatedPresheaves U ⋙ (@PresheafOfModules.sheafification.{u, u, u, u + 1}
        (GroupoidsOver.slice U).total inferInstance
        ((GroupoidsOver.slice U).associatedTopology .fppf)
        _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
        inferInstance inferInstance
        (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
        (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf))

/-- The associated module sheaf is computed by canonical module sheafification. -/
theorem associatedModules_obj (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    (associatedModules U).obj M =
      ((@PresheafOfModules.sheafification.{u, u, u, u + 1}
        (GroupoidsOver.slice U).total inferInstance
        ((GroupoidsOver.slice U).associatedTopology .fppf)
        _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
        inferInstance inferInstance
        (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
        (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf))).obj
        (associatedPresheaf U M) := rfl

/-- The canonical unit maps scalar-extension presheaves to their associated module sheaves. -/
def associatedModulesUnit (U : Over S) [IsAffine U.left] :
    associatedPresheaves U ⟶ associatedModules U ⋙
      SheafOfModules.forget (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj) :=
  Functor.whiskerLeft (associatedPresheaves U)
    ((@PresheafOfModules.sheafificationAdjunction.{u, u, u, u + 1}
        (GroupoidsOver.slice U).total inferInstance
        ((GroupoidsOver.slice U).associatedTopology .fppf)
        _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
        inferInstance inferInstance
        (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
        (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf))).unit

/-- On affine test schemes the sheafification unit identifies tensor sections with sheaf sections. -/
theorem associatedModulesUnit_app_bijective (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) (x : (GroupoidsOver.slice U).totalᵒᵖ)
    [IsAffine x.unop.left.left] :
    Function.Bijective (((associatedModulesUnit U).app M).app x) := sorry

/-- A module associated to a coordinate-ring module on an affine slice is quasi-coherent. -/
theorem associatedQCoh_isQuasicoherent (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    quasiCoherentModuleProperty (GroupoidsOver.slice U) ((associatedModules U).obj M) := sorry

/-- The quasi-coherent module functor associated to modules over an affine coordinate ring. -/
def associatedQCoh (U : Over S) [IsAffine U.left] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤ QCoh (GroupoidsOver.slice U) :=
  (quasiCoherentModuleProperty (GroupoidsOver.slice U)).lift
    (associatedModules U) (associatedQCoh_isQuasicoherent U)

/-- The underlying sheaf of an associated quasi-coherent module is the associated module sheaf. -/
theorem associatedQCoh_obj (U : Over S) [IsAffine U.left]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    ((associatedQCoh U).obj M).obj = (associatedModules U).obj M := rfl

private def coordinateUnitIso (U : Over S) (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    associatedExtend U (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) x ≅
      (structureSheaf (GroupoidsOver.slice U)).obj.val.obj x :=
  (@TensorProduct.AlgebraTensorModule.rid Γ(U.left, ⊤) Γ(x.unop.left.left, ⊤)
    (coefficients U x) inferInstance inferInstance
    (associatedSectionHom U x).toAlgebra inferInstance inferInstance inferInstance
    (@IsScalarTower.mk Γ(U.left, ⊤) Γ(x.unop.left.left, ⊤) (coefficients U x)
      (associatedSectionHom U x).toAlgebra.toSMul
      (inferInstance : Module Γ(x.unop.left.left, ⊤) (coefficients U x)).toSMul
      (coefficients U x).isModule.toSMul
      (fun a b c ↦ mul_assoc (associatedSectionHom U x a) b c))).toModuleIso

/-- The scalar-extension identification with the structure module commutes with restrictions. -/
theorem associatedQCohStructureSheaf_laws (U : Over S) [IsAffine U.left] :
    (∀ {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y),
      (associatedPresheaf U (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))).map f ≫
          (ModuleCat.restrictScalars
            ((GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.map f).hom).map
            (coordinateUnitIso U y).hom =
        (coordinateUnitIso U x).hom ≫ (structureSheaf (GroupoidsOver.slice U)).obj.val.map f) ∧
    (∀ x, (coordinateUnitIso U x).hom ≫ (coordinateUnitIso U x).inv = 𝟙 _) ∧
    (∀ x, (coordinateUnitIso U x).inv ≫ (coordinateUnitIso U x).hom = 𝟙 _) := sorry

/-- The module associated to the affine coordinate ring is the structure module,
via the sectionwise identification `Γ(T) ⊗[A] A ≅ Γ(T)`. -/
def associatedQCohStructureSheafIso (U : Over S) [IsAffine U.left] :
    (associatedQCoh U).obj (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) ≅
      structureSheaf (GroupoidsOver.slice U) := by
  let sheafify := @PresheafOfModules.sheafification.{u, u, u, u + 1}
    (GroupoidsOver.slice U).total inferInstance
    ((GroupoidsOver.slice U).associatedTopology .fppf)
    _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
    inferInstance inferInstance
    (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
    (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf)
  let adj := @PresheafOfModules.sheafificationAdjunction.{u, u, u, u + 1}
    (GroupoidsOver.slice U).total inferInstance
    ((GroupoidsOver.slice U).associatedTopology .fppf)
    _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
    inferInstance inferInstance
    (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
    (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf)
  let counitIso := @asIso _ _ _ _ adj.counit
    (@PresheafOfModules.instIsIsoFunctorSheafOfModulesCounitSheafificationAdjunction.{u, u, u, u + 1}
      (GroupoidsOver.slice U).total inferInstance
      ((GroupoidsOver.slice U).associatedTopology .fppf)
      _ (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)) (𝟙 _)
      inferInstance inferInstance
      (associatedTopology_wEqualsLocallyBijective (GroupoidsOver.slice U) .fppf)
      (associatedTopology_hasWeakSheafify (GroupoidsOver.slice U) .fppf))
  exact (quasiCoherentModuleProperty (GroupoidsOver.slice U)).isoMk
    (sheafify.mapIso
      (PresheafOfModules.isoMk (coordinateUnitIso U)
        (fun {x y} f ↦ (associatedQCohStructureSheaf_laws U).1 f) ≪≫
        PresheafOfModules.Restriction.idComponentIso'
          (𝟙 (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj) rfl
          (structureSheaf (GroupoidsOver.slice U)).obj.val) ≪≫
      counitIso.app (structureSheaf (GroupoidsOver.slice U)).obj)

private def mulLeftApp (U : Over S) (a : Γ(U.left, ⊤))
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    (structureSheaf (GroupoidsOver.slice U)).obj.val.obj x ⟶
      (structureSheaf (GroupoidsOver.slice U)).obj.val.obj x :=
  ModuleCat.ofHom
    (X := (structureSheaf (GroupoidsOver.slice U)).obj.val.obj x)
    (Y := (structureSheaf (GroupoidsOver.slice U)).obj.val.obj x)
    (LinearMap.mulLeft Γ(x.unop.left.left, ⊤) (associatedSectionHom U x a))

/-- Coordinate multiplication is linear and commutes with structure-sheaf restrictions. -/
theorem structureSheafMulLeft_module_laws (U : Over S) (a : Γ(U.left, ⊤)) :
    (∀ (x : (GroupoidsOver.slice U).totalᵒᵖ) (r : (GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.obj x) m,
      mulLeftApp U a x (r • m) = r • mulLeftApp U a x m) ∧
    (∀ {x y : (GroupoidsOver.slice U).totalᵒᵖ} (f : x ⟶ y),
      (structureSheaf (GroupoidsOver.slice U)).obj.val.map f ≫
          (ModuleCat.restrictScalars
            ((GroupoidsOver.structureSheaf (GroupoidsOver.slice U)).obj.map f).hom).map
            (mulLeftApp U a y) =
        mulLeftApp U a x ≫ (structureSheaf (GroupoidsOver.slice U)).obj.val.map f) := sorry

/-- Multiplication by a global coordinate section on the structure module sheaf. -/
def structureSheafMulLeft_module (U : Over S) (a : Γ(U.left, ⊤)) :
    (structureSheaf (GroupoidsOver.slice U)).obj ⟶
      (structureSheaf (GroupoidsOver.slice U)).obj where
  val.app := mulLeftApp U a
  val.naturality := (structureSheafMulLeft_module_laws U a).2

/-- Multiplication by a global coordinate section as a quasi-coherent endomorphism. -/
def structureSheafMulLeft (U : Over S) (a : Γ(U.left, ⊤)) :
    structureSheaf (GroupoidsOver.slice U) ⟶ structureSheaf (GroupoidsOver.slice U) :=
  homMk (structureSheafMulLeft_module U a)

end AlgebraicGeometry.GroupoidsOver.QCoh

