/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerStructureMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CharacterTwist
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-!
# Integer character twists of modules

The canonical ring-presheaf map `ℤ̲ ⟶ 𝒪_U` extends scalars of the character sheaf
`ℤ̲(χ)` pointwise. Sheafifying its tensor with a universe-lifted module realizes
`F ⊗_ℤ ℤ̲(χ)` as a structure-sheaf module and preserves quasi-coherence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

-- The local sheafification certificates are private Prop-valued proofs.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

private theorem characterTwist_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1} := by
  letI := smallEtaleTopology_hasSheafify_addCommGrpCat X
  exact HasSheafify.isRightAdjoint

private theorem characterTwist_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  smallEtaleTopology_wEqualsLocallyBijective_addCommGrpCat X

-- Use the proved sheafification owners for these Prop parameters, so that the
-- chosen left adjoint does not rely on the admitted successor-universe instances.
attribute [local instance 2000] characterTwist_hasWeakSheafify characterTwist_wEqualsLocallyBijective

variable {W U : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
variable (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)

/-- Sections of `ℤ̲(χ)` over an étale object, viewed as a module over `ULift ℤ`. -/
noncomputable def integerCharacterSection (V : (smallEtaleSite U)ᵒᵖ) :
    ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
  (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom).obj
    (ModuleCat.of ℤ ((integerCharacterAbelianSheaf ρ q χ).obj.obj V))

/-- `integerCharacterSection` is restriction of scalars of the abelian sections of
`ℤ̲(χ)` along `ULift.ringEquiv`. -/
theorem integerCharacterSection_def (V : (smallEtaleSite U)ᵒᵖ) :
    integerCharacterSection ρ q χ V =
      (ModuleCat.restrictScalars
          (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom).obj
        (ModuleCat.of ℤ ((integerCharacterAbelianSheaf ρ q χ).obj.obj V)) :=
  rfl

/-- Restriction of `integerCharacterSection` along an étale arrow. -/
noncomputable def integerCharacterSectionRestrict
    {V W : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ W) :
    ModuleCat.Hom (integerCharacterSection ρ q χ V)
      (integerCharacterSection ρ q χ W) :=
  ModuleCat.ofHom
    (X := integerCharacterSection ρ q χ V)
    (Y := integerCharacterSection ρ q χ W)
    { toFun := fun m ↦ (integerCharacterAbelianSheaf ρ q χ).obj.map f m
      map_add' := fun m n ↦ map_add ((integerCharacterAbelianSheaf ρ q χ).obj.map f).hom m n
      map_smul' := fun r m ↦
        map_zsmul ((integerCharacterAbelianSheaf ρ q χ).obj.map f).hom r.down m }

/-- `integerCharacterSectionRestrict` acts by restriction of abelian sections. -/
theorem integerCharacterSectionRestrict_apply
    {V W : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ W)
    (m : integerCharacterSection ρ q χ V) :
    (integerCharacterSectionRestrict ρ q χ f).hom m =
      (integerCharacterAbelianSheaf ρ q χ).obj.map f m :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise scalar extension of `ℤ̲(χ)` along `integerToStructurePresheaf`. -/
noncomputable def integerCharacterExtendScalarsPresheaf :
    PresheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)
        (commStructureSheafLift U)).obj where
  obj V :=
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        ((integerToStructurePresheaf U).app V).hom).obj
      (integerCharacterSection ρ q χ V)
  map {V W} f :=
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((integerToStructurePresheaf U).app V).hom).homEquiv _ _).symm
      (integerCharacterSectionRestrict ρ q χ f ≫
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
            ((integerToStructurePresheaf U).app W).hom).unit.app
          (integerCharacterSection ρ q χ W) ≫
        (ModuleCat.restrictScalarsComp'App.{u + 1, u + 1, u + 1, u + 1}
            ((integerToStructurePresheaf U).app V).hom
            ((commStructureSheafLift U).obj.map f).hom
            ((integerToStructurePresheaf U).app W).hom (by
              ext r
              exact (map_intCast ((commStructureSheafLift U).obj.map f).hom r.down).symm)
            ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
                ((integerToStructurePresheaf U).app W).hom).obj
              (integerCharacterSection ρ q χ W))).hom)
  map_id V := by
    apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      ((integerToStructurePresheaf U).app V).hom).homEquiv _ _).injective
    ext m
    simp [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
      integerCharacterSectionRestrict]
    rfl
  map_comp {V W T} f g := by
    let η := fun V ↦
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((integerToStructurePresheaf U).app V).hom).unit.app
          (integerCharacterSection ρ q χ V)
    let φ := fun {V W : (smallEtaleSite U)ᵒᵖ} (h : V ⟶ W) ↦
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          ((integerToStructurePresheaf U).app V).hom).homEquiv _ _).symm
        (integerCharacterSectionRestrict ρ q χ h ≫
          (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
              ((integerToStructurePresheaf U).app W).hom).unit.app
            (integerCharacterSection ρ q χ W) ≫
          (ModuleCat.restrictScalarsComp'App.{u + 1, u + 1, u + 1, u + 1}
              ((integerToStructurePresheaf U).app V).hom
              ((commStructureSheafLift U).obj.map h).hom
              ((integerToStructurePresheaf U).app W).hom (by
                ext r
                exact (map_intCast ((commStructureSheafLift U).obj.map h).hom r.down).symm)
              ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
                  ((integerToStructurePresheaf U).app W).hom).obj
                (integerCharacterSection ρ q χ W))).hom)
    have hφ {V W : (smallEtaleSite U)ᵒᵖ} (h : V ⟶ W)
        (m : integerCharacterSection ρ q χ V) :
        φ h ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          ((integerToStructurePresheaf U).app V).hom).unit.app _ m) =
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          ((integerToStructurePresheaf U).app W).hom).unit.app _
            ((integerCharacterSectionRestrict ρ q χ h).hom m) := by
      change (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((integerToStructurePresheaf U).app V).hom).homEquiv _ _) (φ h)).hom m = _
      dsimp only [φ]
      rw [Equiv.apply_symm_apply]
      rfl
    apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      ((integerToStructurePresheaf U).app V).hom).homEquiv _ _).injective
    ext m
    change φ (f ≫ g) (η V m) = φ g (φ f (η V m))
    calc
      φ (f ≫ g) (η V m) = η T ((integerCharacterSectionRestrict ρ q χ (f ≫ g)).hom m) :=
        hφ (f ≫ g) m
      _ = η T ((integerCharacterSectionRestrict ρ q χ g).hom
          ((integerCharacterSectionRestrict ρ q χ f).hom m)) :=
        congrArg (fun s : integerCharacterSection ρ q χ T ↦ η T s)
          (CategoryTheory.congr_fun ((integerCharacterAbelianSheaf ρ q χ).obj.map_comp f g) m)
      _ = φ g (η W ((integerCharacterSectionRestrict ρ q χ f).hom m)) :=
        (hφ g _).symm
      _ = φ g (φ f (η V m)) := congrArg (fun s ↦ φ g s) (hφ f m).symm

/-- On each étale object, `integerCharacterExtendScalarsPresheaf` is
`ModuleCat.extendScalars` of `integerCharacterSection`. -/
theorem integerCharacterExtendScalarsPresheaf_obj (V : (smallEtaleSite U)ᵒᵖ) :
    (integerCharacterExtendScalarsPresheaf ρ q χ).obj V =
      (ModuleCat.extendScalars ((integerToStructurePresheaf U).app V).hom).obj
        (integerCharacterSection ρ q χ V) :=
  rfl

/-- The `𝒪_U`-module `𝒪_U ⊗_ℤ ℤ̲(χ)`, obtained by sheafifying the pointwise
scalar extension of the character sheaf. -/
noncomputable def integerCharacterModule :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U) :=
  (PresheafOfModules.sheafification
      (𝟙 (commRingedSiteLift U).structureSheaf.obj)).obj
    (integerCharacterExtendScalarsPresheaf ρ q χ)

/-- `integerCharacterModule` is module sheafification of
`integerCharacterExtendScalarsPresheaf`. -/
theorem integerCharacterModule_def :
    integerCharacterModule ρ q χ =
      (PresheafOfModules.sheafification
          (𝟙 (commRingedSiteLift U).structureSheaf.obj)).obj
        (integerCharacterExtendScalarsPresheaf ρ q χ) :=
  rfl

/-- The scalar extension `𝒪_U ⊗_ℤ ℤ̲(χ)` is quasi-coherent. -/
instance integerCharacterModule_isQuasicoherent :
    (integerCharacterModule ρ q χ).IsQuasicoherent :=
  sorry

/-- Pointwise tensor of a universe-lifted `𝒪_U`-module with the scalar extension
of `ℤ̲(χ)`. -/
noncomputable def tensorIntegerCharacterModulePresheaf (F : U.Modules) :
    PresheafOfModules.{u + 1} (commRingedSiteLift U).structureSheaf.obj :=
  PresheafOfModules.Monoidal.tensorObj (Modules.liftModule F).val
    (integerCharacterExtendScalarsPresheaf ρ q χ)

/-- `tensorIntegerCharacterModulePresheaf` is the presheaf tensor of
`Modules.liftModule F` with `integerCharacterExtendScalarsPresheaf`. -/
theorem tensorIntegerCharacterModulePresheaf_def (F : U.Modules) :
    tensorIntegerCharacterModulePresheaf ρ q χ F =
      PresheafOfModules.Monoidal.tensorObj (Modules.liftModule F).val
        (integerCharacterExtendScalarsPresheaf ρ q χ) :=
  rfl

/-- The `𝒪_U`-module `F ⊗_ℤ ℤ̲(χ)`, obtained by sheafifying the pointwise tensor
of the universe-lifted module `F` with `𝒪_U ⊗_ℤ ℤ̲(χ)`. -/
noncomputable def tensorIntegerCharacterModule (F : U.Modules) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U) :=
  (PresheafOfModules.sheafification
      (𝟙 (commRingedSiteLift U).structureSheaf.obj)).obj
    (tensorIntegerCharacterModulePresheaf ρ q χ F)

/-- `tensorIntegerCharacterModule` is module sheafification of
`tensorIntegerCharacterModulePresheaf`. -/
theorem tensorIntegerCharacterModule_def (F : U.Modules) :
    tensorIntegerCharacterModule ρ q χ F =
      (PresheafOfModules.sheafification
          (𝟙 (commRingedSiteLift U).structureSheaf.obj)).obj
        (tensorIntegerCharacterModulePresheaf ρ q χ F) :=
  rfl

/-- As abelian sheaves, sheafification of `tensorIntegerCharacterModulePresheaf`
is the module-sheaf forgetful image of `tensorIntegerCharacterModule`. -/
noncomputable def tensorIntegerCharacterModule_toSheaf (F : U.Modules) :
    (SheafOfModules.toSheaf (commRingedSiteLift U).structureSheaf).obj
        (tensorIntegerCharacterModule ρ q χ F) ≅
      (presheafToSheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}).obj
        ((PresheafOfModules.toPresheaf _).obj
          (tensorIntegerCharacterModulePresheaf ρ q χ F)) :=
  (PresheafOfModules.sheafificationCompToSheaf
      (𝟙 (commRingedSiteLift U).structureSheaf.obj)).app
    (tensorIntegerCharacterModulePresheaf ρ q χ F)

/-- The underlying abelian sheaf of `tensorIntegerCharacterModule ρ q χ F` is
isomorphic to `tensorIntegerCharacter ρ q χ` of the underlying abelian sheaf of
`Modules.liftModule F`. The comparison is the existing
`tensorIntegerCharacterModule_toSheaf` isomorphism, composed with the canonical
identification of the sheafified `𝒪`-tensor with the `ℤ`-tensor of abelian
sheaves. -/
theorem tensorIntegerCharacterModule_toSheaf_spec (F : U.Modules) :
    IsIsomorphic
      ((SheafOfModules.toSheaf (commRingedSiteLift U).structureSheaf).obj
        (tensorIntegerCharacterModule ρ q χ F))
      (tensorIntegerCharacter ρ q χ
        ((SheafOfModules.toSheaf (commRingedSiteLift U).structureSheaf).obj
          (Modules.liftModule F))) :=
  sorry

/-- Tensoring a quasi-coherent structure-sheaf module with the integer character
sheaf associated to a finite free action preserves quasi-coherence. -/
@[stacks 072A, instance]
instance tensorIntegerCharacterModule_isQuasicoherent (F : U.Modules)
    [F.IsQuasicoherent] :
    (tensorIntegerCharacterModule ρ q χ F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
