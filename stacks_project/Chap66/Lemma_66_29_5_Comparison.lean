/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

/-!
# Pullback-stalk comparison for modules on algebraic spaces

A morphism of algebraic spaces induces a map of étale local rings at a geometric point and
its image. Scalar extension along that map compares the stalk of a pulled-back module with
the stalk of the original module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules
open ModuleCat Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Forgetting the ring structure preserves filtered colimits of size `u`. -/
instance forget_ringCat_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u} (forget RingCat.{u}) :=
  inferInstance

/-- The inverse-image structure sheaf `f⁻¹ 𝒪_Y` on `X_étale`. -/
def inverseImageStructureSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) RingCat.{u} :=
  (ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)

/-- The inverse-image structure sheaf is the ring-valued inverse image of `𝒪_Y`. -/
theorem inverseImageStructureSheaf_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    inverseImageStructureSheaf f =
      (ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y) :=
  rfl

/-- The stalk of `f⁻¹ 𝒪_Y` at a geometric point of `X`, as a `RingCat` object. -/
def inverseImageEtaleLocalRingCat {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) : RingCat.{u} :=
  ((toSmallEtalePoint xbar).presheafFiber).obj (inverseImageStructureSheaf f).obj

/-- The stalk of `f⁻¹ 𝒪_Y` is the site-point fibre of `inverseImageStructureSheaf`. -/
theorem inverseImageEtaleLocalRingCat_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    inverseImageEtaleLocalRingCat f xbar =
      ((toSmallEtalePoint xbar).presheafFiber).obj (inverseImageStructureSheaf f).obj :=
  rfl

/-- The map on stalks induced by `f^♯ : f⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
def inverseImageStructureSheaf_stalkMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    inverseImageEtaleLocalRingCat f xbar ⟶
      ((toSmallEtalePoint xbar).presheafFiber).obj (structureSheaf X).obj :=
  (toSmallEtalePoint xbar).presheafFiber.map (ringedToposHom f).structureMap.hom

/-- `inverseImageStructureSheaf_stalkMap` is the fibre of `f^♯`. -/
theorem inverseImageStructureSheaf_stalkMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    inverseImageStructureSheaf_stalkMap f xbar =
      (toSmallEtalePoint xbar).presheafFiber.map (ringedToposHom f).structureMap.hom :=
  rfl

/-- Underlying type-valued sheaf of a small-étale ring sheaf. -/
def forgetRingSheaf {X : AlgebraicSpace S} (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    Sheaf (smallEtaleTopology X) (Type u) :=
  (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj R

/-- The type-valued stalk of a ring sheaf is the underlying type of its `RingCat` stalk. -/
def forgetRingSheaf_stalkIso {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    (toSmallEtalePoint xbar).sheafFiber.obj (forgetRingSheaf R) ≅
      (forget RingCat.{u}).obj ((toSmallEtalePoint xbar).presheafFiber.obj R.obj) :=
  ((toSmallEtalePoint xbar).sheafFiberCompIso (forget RingCat.{u})).app R

/-- Underlying type sheaf of `f⁻¹ 𝒪_Y` identifies with the inverse image of the underlying
type sheaf of `𝒪_Y`. -/
def inverseImageStructureSheaf_forgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forgetRingSheaf (inverseImageStructureSheaf f) ≅
      (morphismOfTopoi f).inverseImage.obj (forgetRingSheaf (structureSheaf Y)) :=
  (ringedToposHom f).toTopos.ringInverseImageForgetIso.app (structureSheaf Y)

/-- Send a scheme-étale lift of `x̄` through `U`, together with a map `U ⟶ X ×_Y V` over `X`,
to the induced lift of `ȳ` through `V`. -/
def xLiftToYLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    {V : smallEtaleSite Y} {U : smallEtaleSite X}
    (a : (smallEtaleInclusion X).obj U ⟶ (etaleBaseChange f).obj V)
    (l : OverLift xbar U) : OverLift (xbar.map f) V :=
  OverLift.of (l.hom ≫ toOverHom (a.left ≫ etaleBaseChangeSnd f V)) sorry

/-- Sections of the skyscraper at `ȳ` over `V`, as a cone under the Kan-extension diagram of
the skyscraper at `x̄` evaluated at `X ×_Y V`. -/
def skyscraperPushforwardCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    (E : Type u) (V : (smallEtaleSite Y)ᵒᵖ) :
    Cone
      (StructuredArrow.proj (op ((etaleBaseChange f).obj V.unop))
        (SpacesEtale.AtlasCharts.inclusion X).op ⋙
        ((EtaleTopos.smallEquivalence X).functor.obj
          ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj) where
  pt := ((toSmallEtalePoint (xbar.map f)).skyscraperSheaf E).obj.obj V
  π :=
    { app := fun a ↦
        Pi.lift fun l ↦
          Pi.π (fun _ : (toSmallEtalePoint (xbar.map f)).fiber.obj V.unop ↦ E)
            (xLiftToYLift f xbar a.hom.unop l)
      naturality := fun _ _ _ ↦ sorry }

/-- Component at `V` of the canonical map of skyscraper sheaves `sky_ȳ E ⟶ f_* sky_x̄ E`. -/
def skyscraperPushforwardHom_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (E : Type u) (V : (smallEtaleSite Y)ᵒᵖ) :
    ((toSmallEtalePoint (xbar.map f)).skyscraperSheaf E).obj.obj V ⟶
      ((typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj.obj V :=
  limit.lift _ (skyscraperPushforwardCone f xbar E V) ≫
    ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj
          ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

/-- Canonical comparison `sky_ȳ E ⟶ f_* sky_x̄ E` of type-valued skyscraper sheaves. -/
def skyscraperPushforwardHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    (E : Type u) :
    (toSmallEtalePoint (xbar.map f)).skyscraperSheaf E ⟶
      (typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E) :=
  InducedCategory.homMk
    { app := fun V ↦ skyscraperPushforwardHom_app f xbar E V
      naturality := fun _ _ _ ↦ sorry }

/-- The comparisons `sky_ȳ ⟶ f_* sky_x̄` are natural in the coefficient type. -/
def skyscraperPushforwardNatTrans {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    (toSmallEtalePoint (xbar.map f)).skyscraperSheafFunctor ⟶
      (toSmallEtalePoint xbar).skyscraperSheafFunctor ⋙ typePushforward f where
  app E := skyscraperPushforwardHom f xbar E
  naturality := fun _ _ _ ↦ sorry

/-- Type-valued inverse-image stalks along `morphismOfTopoi f` map to stalks at `ȳ = f ∘ x̄`. -/
def typeInverseImageStalkHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    (morphismOfTopoi f).inverseImage ⋙ (toSmallEtalePoint xbar).sheafFiber ⟶
      (toSmallEtalePoint (xbar.map f)).sheafFiber :=
  (conjugateEquiv
      ((toSmallEtalePoint (xbar.map f)).skyscraperSheafAdjunction (A := Type u))
      ((morphismOfTopoi f).adjunction.comp
        ((toSmallEtalePoint xbar).skyscraperSheafAdjunction (A := Type u)))).symm
    (skyscraperPushforwardNatTrans f xbar)

/-- The inverse-image type stalk of `𝒪_Y` at `x̄` is nonempty, as it is the underlying type of a
ring. -/
theorem inverseImageForgetStalkNonempty {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    Nonempty
      ((toSmallEtalePoint xbar).sheafFiber.obj
        ((morphismOfTopoi f).inverseImage.obj (forgetRingSheaf (structureSheaf Y)))) :=
  ⟨(toSmallEtalePoint xbar).sheafFiber.map (inverseImageStructureSheaf_forgetIso f).hom
      ((forgetRingSheaf_stalkIso xbar (inverseImageStructureSheaf f)).inv
        (0 : (forget RingCat.{u}).obj (inverseImageEtaleLocalRingCat f xbar)))⟩

/-- Canonical identification of `𝒪_{Y, ȳ}` with the stalk of `f⁻¹ 𝒪_Y` at `x̄`, as types. -/
def inverseImageStructureSheafStalkTypeIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    (forget RingCat.{u}).obj
        (((toSmallEtalePoint (xbar.map f)).presheafFiber).obj (structureSheaf Y).obj) ≅
      (forget RingCat.{u}).obj (inverseImageEtaleLocalRingCat f xbar) :=
  (forgetRingSheaf_stalkIso (xbar.map f) (structureSheaf Y)).symm ≪≫
    Equiv.toIso
      { toFun :=
          @invFun _ _ (inverseImageForgetStalkNonempty f xbar)
            ((typeInverseImageStalkHom f xbar).app (forgetRingSheaf (structureSheaf Y)))
        invFun :=
          (typeInverseImageStalkHom f xbar).app (forgetRingSheaf (structureSheaf Y))
        left_inv := sorry
        right_inv := sorry } ≪≫
    ((toSmallEtalePoint xbar).sheafFiber.mapIso
      (inverseImageStructureSheaf_forgetIso f).symm) ≪≫
    forgetRingSheaf_stalkIso xbar (inverseImageStructureSheaf f)

/-- Canonical `RingCat` identification of `𝒪_{Y, ȳ}` with the stalk of `f⁻¹ 𝒪_Y` at `x̄`. -/
def inverseImageStructureSheafStalkIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    ((toSmallEtalePoint (xbar.map f)).presheafFiber).obj (structureSheaf Y).obj ≅
      inverseImageEtaleLocalRingCat f xbar where
  hom :=
    RingCat.ofHom
      { toFun := (inverseImageStructureSheafStalkTypeIso f xbar).hom
        map_zero' := sorry
        map_one' := sorry
        map_add' := sorry
        map_mul' := sorry }
  inv :=
    RingCat.ofHom
      { toFun := (inverseImageStructureSheafStalkTypeIso f xbar).inv
        map_zero' := sorry
        map_one' := sorry
        map_add' := sorry
        map_mul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The local ring map `𝒪_{Y, ȳ} →+* 𝒪_{X, x̄}` associated to a morphism of algebraic spaces,
where `ȳ = xbar.map f`. -/
def etaleLocalRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    etaleLocalRing Y (xbar.map f) →+* etaleLocalRing X xbar :=
  RingCat.Hom.hom
    ((inverseImageStructureSheafStalkIso f xbar).hom ≫
      inverseImageStructureSheaf_stalkMap f xbar)

/-- `etaleLocalRingMap` is the stalk of `f^♯` after identifying inverse-image stalks with
étale local rings at `ȳ`. -/
theorem etaleLocalRingMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    etaleLocalRingMap f xbar =
      RingCat.Hom.hom
        ((inverseImageStructureSheafStalkIso f xbar).hom ≫
          inverseImageStructureSheaf_stalkMap f xbar) :=
  rfl

/-- The local ring map of a composite morphism is the composite of the local ring maps. -/
theorem etaleLocalRingMap_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (xbar : GeometricPoint X) :
    etaleLocalRingMap (f ≫ g) xbar =
      (etaleLocalRingMap f xbar).comp (etaleLocalRingMap g (xbar.map f)) :=
  sorry

/-- The local ring map of an identity morphism is the identity. -/
theorem etaleLocalRingMap_id {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    etaleLocalRingMap (𝟙 X) xbar = RingHom.id (etaleLocalRing X xbar) :=
  sorry

namespace Modules

variable {X Y : AlgebraicSpace S}

/-- Underlying type-valued sheaf of an `𝒪`-module on the small étale site. -/
def typeSheaf (Z : AlgebraicSpace S) :
    Z.Modules ⥤ Sheaf (smallEtaleTopology Z) (Type u) :=
  SheafOfModules.toSheaf (structureSheaf Z) ⋙
    sheafCompose (smallEtaleTopology Z) (forget AddCommGrpCat.{u})

/-- The zero section of the underlying type sheaf of a module, as a map from the terminal
sheaf. -/
def typeSheafZeroHom (Z : AlgebraicSpace S) (F : Z.Modules) :
    Sheaf.terminal (smallEtaleTopology Z) Types.isTerminalPUnit ⟶ (typeSheaf Z).obj F :=
  InducedCategory.homMk
    { app := fun U ↦
        TypeCat.ofHom fun _ ↦
          (0 :
            (forget AddCommGrpCat.{u}).obj
              (((SheafOfModules.toSheaf (structureSheaf Z)).obj F).obj.obj U))
      naturality := fun _ _ _ ↦ sorry }

/-- The additive group of an étale module stalk is the site-point fibre of the underlying
additive presheaf. -/
def stalkModuleCat_addIso {Z : AlgebraicSpace S} (xbar : GeometricPoint Z) (F : Z.Modules) :
    (forget₂ (ModuleCat (etaleLocalRing Z xbar)) AddCommGrpCat.{u}).obj (stalkModuleCat xbar F) ≅
      (toSmallEtalePoint xbar).presheafFiber.obj F.val.presheaf :=
  Iso.refl _

/-- The underlying type of an étale module stalk identifies with the type-valued sheaf fibre. -/
def stalkModuleCat_typeIso {Z : AlgebraicSpace S} (xbar : GeometricPoint Z) (F : Z.Modules) :
    (forget (ModuleCat (etaleLocalRing Z xbar))).obj (stalkModuleCat xbar F) ≅
      (toSmallEtalePoint xbar).sheafFiber.obj ((typeSheaf Z).obj F) :=
  (forget AddCommGrpCat.{u}).mapIso (stalkModuleCat_addIso xbar F) ≪≫
    ((toSmallEtalePoint xbar).sheafFiberCompIso (forget AddCommGrpCat.{u})).symm.app
      ((SheafOfModules.toSheaf (structureSheaf Z)).obj F)

/-- Zero in the inverse-image type stalk of a module, obtained by applying inverse image to the
zero section. -/
def inverseImageTypeSheafStalkZero (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    (toSmallEtalePoint xbar).sheafFiber.obj
      ((morphismOfTopoi f).inverseImage.obj ((typeSheaf Y).obj G)) :=
  ConcreteCategory.hom
      ((toSmallEtalePoint xbar).sheafFiber.map
        ((morphismOfTopoi f).inverseImage.map (typeSheafZeroHom Y G)))
    (ConcreteCategory.hom
        ((toSmallEtalePoint xbar).sheafFiber.map
          (morphismOfTopoi f).inverseImageTerminalIso.inv)
      (ConcreteCategory.hom
          (((Sheaf.isTerminalTerminal (smallEtaleTopology X) Types.isTerminalPUnit).isTerminalObj
                (toSmallEtalePoint xbar).sheafFiber _).uniqueUpToIso
              Types.isTerminalPUnit).inv
        PUnit.unit))

/-- Additive comparison from the stalk of `𝒢` at `ȳ` to the stalk of `f* 𝒢` at `x̄`. -/
def pullbackStalkAddHom (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    AddCommGrpCat.of (stalkModuleCat (xbar.map f) G) ⟶
      AddCommGrpCat.of (stalkModuleCat xbar ((pullback f).obj G)) :=
  AddCommGrpCat.ofHom
    { toFun := fun m ↦
        (stalkModuleCat_typeIso xbar ((pullback f).obj G)).inv
          ((toSmallEtalePoint xbar).sheafFiber.map
              (((morphismOfTopoi f).adjunction.homEquiv
                  ((typeSheaf Y).obj G)
                  ((typeSheaf X).obj ((pullback f).obj G))).symm
                ((typeSheaf Y).map ((Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
                  (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).hom.app
                    ((pullback f).obj G)))
            (@invFun _ _ ⟨inverseImageTypeSheafStalkZero f G xbar⟩
              ((typeInverseImageStalkHom f xbar).app ((typeSheaf Y).obj G))
              ((stalkModuleCat_typeIso (xbar.map f) G).hom m)))
      map_zero' := sorry
      map_add' := sorry }

/-- The `𝒪_{Y, ȳ}`-linear comparison from `𝒢_ȳ` to the stalk of `f* 𝒢` at `x̄`, after
restricting scalars along `etaleLocalRingMap`. -/
def pullbackStalkUnitHom (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    stalkModuleCat (xbar.map f) G ⟶
      (restrictScalars (etaleLocalRingMap f xbar)).obj
        (stalkModuleCat xbar ((pullback f).obj G)) :=
  (semilinearMapAddEquiv (etaleLocalRingMap f xbar)
      (stalkModuleCat (xbar.map f) G)
      (stalkModuleCat xbar ((pullback f).obj G)))
    { toFun := (pullbackStalkAddHom f G xbar).hom
      map_add' := (pullbackStalkAddHom f G xbar).hom.map_add
      map_smul' := sorry }

/-- `pullbackStalkUnitHom` is `𝒪_{Y, ȳ}`-linear. -/
theorem pullbackStalkUnitHom_smul (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X)
    (r : etaleLocalRing Y (xbar.map f)) (m : stalkModuleCat (xbar.map f) G) :
    pullbackStalkUnitHom f G xbar (r • m) =
      etaleLocalRingMap f xbar r • pullbackStalkUnitHom f G xbar m :=
  sorry

/-- Canonical comparison
`(f* 𝒢)_x̄` against `𝒢_ȳ ⊗_{𝒪_{Y, ȳ}} 𝒪_{X, x̄}`,
obtained by extending scalars along `etaleLocalRingMap`. -/
def pullbackStalkComparison (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    (extendScalars (etaleLocalRingMap f xbar)).obj (stalkModuleCat (xbar.map f) G) ⟶
      stalkModuleCat xbar ((pullback f).obj G) :=
  ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (etaleLocalRingMap f xbar)
    (pullbackStalkUnitHom f G xbar)

/-- `pullbackStalkComparison` is the adjunction transpose of `pullbackStalkUnitHom`. -/
theorem pullbackStalkComparison_def (f : X ⟶ Y) (G : Y.Modules) (xbar : GeometricPoint X) :
    pullbackStalkComparison f G xbar =
      ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (etaleLocalRingMap f xbar)
        (pullbackStalkUnitHom f G xbar) :=
  rfl

end Modules

end AlgebraicGeometry.AlgebraicSpace
