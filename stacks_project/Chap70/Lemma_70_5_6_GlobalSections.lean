module

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
      (moduleInverseImageUnitIso f).inv

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

/-- Type-valued direct image along `f`, rewritten through spaces-étale pullback. -/
def typePushforwardFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    typePushforward f ≅
      (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X))
    ((sheafPushforwardContinuousIso (smallEtaleInclusion_comp_spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      sheafPushforwardContinuousComp (smallEtaleInclusion Y) (spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The small étale inclusion is cover-dense in the spaces étale topology. -/
instance smallEtaleInclusion_isCoverDense (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y) :=
  sorry

/-- Spaces-étale pullback along a composite is continuous because each factor is. -/
instance spacesEtalePullback_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback g ⋙ spacesEtalePullback f).IsContinuous
      (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback g) (spacesEtalePullback f)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Restricting a spaces étale sheaf to the small étale site and extending it back
is isomorphic to the identity. Both 1-cells are the cover-dense extensions of the
canonical adjunction unit and counit on the small site. -/
def smallEtaleInclusionContinuousCocontinuousIso (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) (Type u)) :=
  let restrict :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let extend :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  NatIso.ofComponents
    (fun F ↦
      let eSmall : restrict.obj ((restrict ⋙ extend).obj F) ≅ restrict.obj F :=
        { hom := adj.counit.app (restrict.obj F)
          inv := restrict.map (adj.unit.app F)
          hom_inv_id := sorry
          inv_hom_id := sorry }
      let i :
          (smallEtaleInclusion Y).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion Y).op ⋙ F.obj :=
        { hom := eSmall.hom.hom
          inv := eSmall.inv.hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      Functor.IsCoverDense.Types.sheafIso i)
    sorry

/-- Type-valued continuous pushforward along spaces-étale pullback respects composition. -/
def spacesEtaleTypePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f) (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X) ≪≫
    sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Type-valued direct image along a composite is the composite of the
type-valued direct images. -/
def typePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typePushforward f ⋙ typePushforward g ≅ typePushforward (f ≫ g) :=
  let iX :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pF :=
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleInclusion Z).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (typePushforwardFactor f) (typePushforward g) ≪≫
    Functor.associator iX (pF ⋙ iY) (typePushforward g) ≪≫
    isoWhiskerLeft iX (Functor.associator pF iY (typePushforward g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (typePushforwardFactor g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (Functor.associator iY
          ((smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (smallEtaleInclusionContinuousCocontinuousIso Y) (pG ⋙ iZ) ≪≫
        Functor.leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (Functor.associator pF pG iZ ≪≫
        isoWhiskerRight (spacesEtaleTypePushforwardComp f g) iZ) ≪≫
    (typePushforwardFactor (f ≫ g)).symm

/-- The underlying type-valued sheaf of an iterated module pushforward. -/
def pushforwardCompForgetIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward f ⋙ pushforward g) ⋙
        Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z) ≅
      Sheaf.InternalModule.ToInternal.underlying (structureSheaf X) ⋙
        typePushforward f ⋙ typePushforward g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward f)
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f))
      (typePushforward g) ≪≫
    Functor.associator _ _ _

/-- The underlying type-valued comparison of iterated module pushforward with
pushforward along the composite. -/
def pushforwardCompHomUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward f ⋙ pushforward g).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward (f ≫ g)).obj M) :=
  (pushforwardCompForgetIso f g).hom.app M ≫
    (typePushforwardComp f g).hom.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).inv.app M

/-- The reverse underlying type-valued comparison of composite pushforward. -/
def pushforwardCompInvUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward (f ≫ g)).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward f ⋙ pushforward g).obj M) :=
  (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).hom.app M ≫
    (typePushforwardComp f g).inv.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (pushforwardCompForgetIso f g).inv.app M

/-- The composition of module pushforwards along `f` then `g` identifies with
pushforward along `f ≫ g`. -/
def pushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun M =>
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompHomUnderlying f g M) sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompInvUnderlying f g M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

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
