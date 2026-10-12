/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap69.Lemma_69_17_2_Pullback

/-!
# Global sections of modules on algebraic spaces

Hom-based global sections `Hom(𝒪_X, F)` of a module sheaf on the small étale
ringed site, together with the pullback comparison along a morphism of
algebraic spaces and the pseudofunctoriality isomorphisms for module
pullback and pushforward.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The additive group of global sections of an `𝒪_X`-module, realized as
`Hom(𝒪_X, F)` in `X.Modules`. The Hom-type of sheaves of modules on the large
small-étale site lives in `Type (u + 1)`. -/
def globalSections {X : AlgebraicSpace S} (F : X.Modules) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (SheafOfModules.unit (structureSheaf X) ⟶ F)

/-- Evaluating `globalSections F` recovers the Hom-group `Hom(𝒪_X, F)`. -/
theorem globalSections_obj {X : AlgebraicSpace S} (F : X.Modules) :
    globalSections F = AddCommGrpCat.of (SheafOfModules.unit (structureSheaf X) ⟶ F) :=
  rfl

/-- The map on global sections induced by a morphism of `𝒪_X`-modules, given by
postcomposition on `Hom(𝒪_X, -)`. -/
def globalSectionsMap {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G) :
    globalSections F ⟶ globalSections G :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ => ψ ≫ φ
      map_zero' := sorry
      map_add' := sorry }

/-- Postcomposition on `Hom(𝒪_X, -)` is the underlying function of `globalSectionsMap`. -/
theorem globalSectionsMap_eq {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G)
    (ψ : SheafOfModules.unit (structureSheaf X) ⟶ F) :
    (globalSectionsMap φ).hom ψ = ψ ≫ φ :=
  rfl

/-- The type-valued sheaf underlying the structure module of an algebraic space. -/
def unitCarrierIso (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The type-valued sheaf underlying the unit of `f⁻¹ 𝒪_Y`. -/
def inverseImageUnitCarrierIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Sheaf.InternalModule.ToInternal.underlying
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))).obj
      (SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) ≅
      (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv := { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse image of the structure module of `Y` is the unit module of `f⁻¹ 𝒪_Y`. -/
def moduleInverseImageUnitIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((ringedToposHom f).toTopos.moduleInverseImage (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit
        ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)) where
  hom :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      (((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).hom.app
          (SheafOfModules.unit (structureSheaf Y)) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.inv.app (structureSheaf Y) ≫
        (inverseImageUnitCarrierIso f).inv)
      sorry sorry
  inv :=
    Sheaf.InternalModule.homOfUnderlying
      ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))
      ((inverseImageUnitCarrierIso f).hom ≫
        (ringedToposHom f).toTopos.ringInverseImageForgetIso.hom.app (structureSheaf Y) ≫
        (ringedToposHom f).toTopos.inverseImage.map (unitCarrierIso Y).inv ≫
        ((ringedToposHom f).toTopos.moduleInverseImageForgetIso (structureSheaf Y)).inv.app
          (SheafOfModules.unit (structureSheaf Y)))
      sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The free rank-one module `𝒪_X` maps to the scalar extension of `f⁻¹ 𝒪_Y` by sending
the adjunction unit to a global section of the extended unit module. -/
def extendScalarsUnitFromStructure {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).obj
        (SheafOfModules.unit
          ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y))) :=
  let α := (ringedToposHom f).structureMap
  let Rinv := (ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)
  let M := (SheafOfModules.ChangeOfRings.extendScalars α).obj (SheafOfModules.unit Rinv)
  let s :=
    ((SheafOfModules.restrictScalars α).obj M).unitHomEquiv
      ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction α).unit.app
        (SheafOfModules.unit Rinv))
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk (fun U ↦ s.val U) fun _ _ h ↦ s.property h)

/-- The canonical map `𝒪_X ⟶ f^* 𝒪_Y` inverse to `IdealSubobject.pullbackUnit f`. -/
def structureModulePullbackInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) :=
  extendScalarsUnitFromStructure f ≫
    (SheafOfModules.ChangeOfRings.extendScalars (ringedToposHom f).structureMap).map
      (moduleInverseImageUnitIso f).inv ≫
    (pullbackIsoTopos f).inv.app (SheafOfModules.unit (structureSheaf Y))

/-- The canonical identification `𝒪_X ≅ f^* 𝒪_Y` of structure modules. -/
def structureModulePullbackIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit (structureSheaf X) ≅
      (pullback f).obj (SheafOfModules.unit (structureSheaf Y)) where
  hom := structureModulePullbackInv f
  inv := IdealSubobject.pullbackUnit f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The pullback map on global sections along `f : X ⟶ Y`. A section
`ψ : 𝒪_Y ⟶ F` is sent to `𝒪_X ⟶ f^* 𝒪_Y ⟶ f^* F`. -/
def globalSectionsPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules) :
    globalSections F ⟶ globalSections ((pullback f).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ ↦ structureModulePullbackInv f ≫ (pullback f).map ψ
      map_zero' := sorry
      map_add' := sorry }

/-- Base change of schemes étale over `Z` along `f ≫ g` identifies with base change
along `g` followed by spaces-étale pullback along `f`. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleInclusion Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- The composition of module pullbacks along `g` then `f` identifies with
pullback along `f ≫ g`. -/
def pullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g)

/-- The component of `pullbackComp` at a module is the indicated 1-cell of the
left-adjoint mate. -/
theorem pullbackComp_hom_app {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules) :
    (pullbackComp f g).hom.app F =
      (Adjunction.leftAdjointCompIso
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g)).hom.app F :=
  rfl

/-- The map on global sections obtained by pulling back first along `g`, then
along `f`, and comparing the resulting module with pullback along `f ≫ g`. -/
def globalSectionsPullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules) :
    globalSections ((pullback g).obj F) ⟶
      globalSections ((pullback (f ≫ g)).obj F) :=
  globalSectionsPullback f ((pullback g).obj F) ≫
    globalSectionsMap ((pullbackComp f g).hom.app F)

/-- Pulling back global sections through `g` and then `f` agrees with the
global-sections pullback map for `f ≫ g`. -/
theorem globalSectionsPullback_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules) :
    globalSectionsPullback g F ≫ globalSectionsPullbackComp f g F =
      globalSectionsPullback (f ≫ g) F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
