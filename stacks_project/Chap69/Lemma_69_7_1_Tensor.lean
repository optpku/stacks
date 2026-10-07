module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap69.Lemma_69_6_5_Twist
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Integer character twists of quasi-coherent modules

The canonical ring-presheaf map `ℤ̲ ⟶ 𝒪_X` extends scalars of the character sheaf
`ℤ̲(χ)` pointwise by `ModuleCat.extendScalars`. Sheafifying the resulting
`𝒪_U`-module presheaf, and the pointwise tensor of a universe-lifted module
against it, realizes `F ⊗_ℤ ℤ̲(χ)` as an `𝒪_U`-module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The constant integer presheaf maps to the universe-lifted structure sheaf by
the unique ring homomorphisms `ULift ℤ →+* 𝒪(V)`. -/
noncomputable def integerToStructurePresheaf (X : AlgebraicSpace S) :
    (Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)) ⟶
      (commStructureSheafLift X).obj where
  app V :=
    CommRingCat.ofHom
      ((Int.castRingHom ((commStructureSheafLift X).obj.obj V)).comp
        (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom)
  naturality := sorry

/-- On each étale object, `integerToStructurePresheaf` is the composite of
`ULift.ringEquiv` with `Int.castRingHom`. -/
theorem integerToStructurePresheaf_app (X : AlgebraicSpace S)
    (V : (smallEtaleSite X)ᵒᵖ) :
    (integerToStructurePresheaf X).app V =
      CommRingCat.ofHom
        ((Int.castRingHom ((commStructureSheafLift X).obj.obj V)).comp
          (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom) :=
  sorry

/-- The canonical morphism of commutative ring sheaves `ℤ̲ ⟶ 𝒪_X` on the small
étale site, obtained by sheafifying `integerToStructurePresheaf`. -/
noncomputable def integerToStructureSheaf (X : AlgebraicSpace S) :
    constantIntegerRingSheaf X ⟶ commStructureSheafLift X :=
  ((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))
      (commStructureSheafLift X)).symm
    (integerToStructurePresheaf X)

/-- `integerToStructureSheaf` is the sheafification adjunct of
`integerToStructurePresheaf`. -/
theorem integerToStructureSheaf_adjunct (X : AlgebraicSpace S) :
    integerToStructureSheaf X =
      ((sheafificationAdjunction (smallEtaleTopology X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const (smallEtaleSite X)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))
          (commStructureSheafLift X)).symm
        (integerToStructurePresheaf X) :=
  sorry

/-- The underlying morphism of ring sheaves associated to `integerToStructureSheaf`. -/
noncomputable def integerToStructureRingSheafMap (X : AlgebraicSpace S) :
    integerRingSheaf X ⟶ (commRingedSiteLift X).structureSheaf :=
  ringSheafMap.{u + 1, u, u + 1} (integerToStructureSheaf X)

/-- `integerToStructureRingSheafMap` is `ringSheafMap` of `integerToStructureSheaf`. -/
theorem integerToStructureRingSheafMap_def (X : AlgebraicSpace S) :
    integerToStructureRingSheafMap X =
      ringSheafMap.{u + 1, u, u + 1} (integerToStructureSheaf X) :=
  sorry

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
  sorry

/-- Restriction of `integerCharacterSection` along an étale arrow. -/
noncomputable def integerCharacterSectionRestrict
    {V W : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ W) :
    ModuleCat.Hom (integerCharacterSection ρ q χ V)
      (integerCharacterSection ρ q χ W) :=
  ModuleCat.ofHom
    (X := integerCharacterSection ρ q χ V)
    (Y := integerCharacterSection ρ q χ W)
    { toFun := fun m ↦ (integerCharacterAbelianSheaf ρ q χ).obj.map f m
      map_add' := sorry
      map_smul' := sorry }

/-- `integerCharacterSectionRestrict` acts by restriction of abelian sections. -/
theorem integerCharacterSectionRestrict_apply
    {V W : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ W)
    (m : integerCharacterSection ρ q χ V) :
    (integerCharacterSectionRestrict ρ q χ f).hom m =
      (integerCharacterAbelianSheaf ρ q χ).obj.map f m :=
  sorry

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
            ((integerToStructurePresheaf U).app W).hom sorry
            ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
                ((integerToStructurePresheaf U).app W).hom).obj
              (integerCharacterSection ρ q χ W))).hom)
  map_id := sorry
  map_comp := sorry

/-- On each étale object, `integerCharacterExtendScalarsPresheaf` is
`ModuleCat.extendScalars` of `integerCharacterSection`. -/
theorem integerCharacterExtendScalarsPresheaf_obj (V : (smallEtaleSite U)ᵒᵖ) :
    (integerCharacterExtendScalarsPresheaf ρ q χ).obj V =
      (ModuleCat.extendScalars ((integerToStructurePresheaf U).app V).hom).obj
        (integerCharacterSection ρ q χ V) :=
  sorry

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
  sorry

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
  sorry

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
  sorry

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

end AlgebraicGeometry.AlgebraicSpace
