/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveThickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Supported
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Differences and conormal factorizations for first-order thickenings

The ordered difference of two lifted structure maps is compared with the composite
of restriction, a relative derivation, and the first-order conormal inclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open Sheaf.InternalModule RingedSite.ToposHom
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- The inverse-image form of `(a')^♯ - (b')^♯` on `X_spaces,étale`. -/
def structureMapDifference {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    (forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY) ⟶
      (forgetSpacesRing X).obj (closedStructureSheaf iX) :=
  (forgetSpacesRing X).map (structureMap_transported iX iY a a' ha') -
    (forgetSpacesRing X).map (structureMap_transported iX iY a b' hb')

/-- The transported additive difference is the first structure map minus the second. -/
theorem structureMapDifference_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    structureMapDifference iX iY a a' b' ha' hb' =
      (forgetSpacesRing X).map (structureMap_transported iX iY a a' ha') -
        (forgetSpacesRing X).map (structureMap_transported iX iY a b' hb') :=
  rfl

/-- Sectionwise values of `(a')^♯ - (b')^♯` on `X_spaces,étale`. -/
def structureMapDifference_apply {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY)
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf a iY).obj.obj V) :
    (closedStructureSheaf iX).obj.obj V :=
  (structureMap_transported iX iY a a' ha').hom.app V x -
    (structureMap_transported iX iY a b' hb').hom.app V x

/-- The value of the transported difference on a section is the difference of the two values. -/
theorem structureMapDifference_apply_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY)
    (V : (spacesEtaleSite X)ᵒᵖ)
    (x : (inverseImageClosedStructureSheaf a iY).obj.obj V) :
    structureMapDifference_apply iX iY a a' b' ha' hb' V x =
      (structureMap_transported iX iY a a' ha').hom.app V x -
        (structureMap_transported iX iY a b' hb').hom.app V x :=
  rfl

/-- The additive difference of `(a')^♯` and `(b')^♯`, restricted to `X_étale`. -/
def structureMapDifference_restrict {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf iX)) :=
  (EtaleAdditive.restriction X).map (structureMapDifference iX iY a a' b' ha' hb')

/-- The difference on the small étale site is the restriction of the transported difference. -/
theorem structureMapDifference_restrict_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    (ha' : iX ≫ a' = a ≫ iY) (hb' : iX ≫ b' = a ≫ iY) :
    structureMapDifference_restrict iX iY a a' b' ha' hb' =
      (EtaleAdditive.restriction X).map (structureMapDifference iX iY a a' b' ha' hb') :=
  rfl

/-- The first-order action `I ⊗ I ⟶ I` followed by the identity on `I` vanishes. -/
theorem firstOrderIdealAction_comp_id {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ≫
      𝟙 (Hom.idealSheaf i) = 0 :=
  by
    rw [Category.comp_id]
    exact IsFirstOrderThickening.square_zero

/-- The inverse of `I ⟶ I/I²` on a first-order thickening, as cokernel descent of the
identity along the vanishing action `I ⊗ I ⟶ I`. -/
def firstOrderQuotientInv {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ⟶
      Hom.idealSheaf i :=
  cokernel.desc
    (Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i))
    (𝟙 (Hom.idealSheaf i)) (firstOrderIdealAction_comp_id i)

/-- The inverse conormal quotient map is the cokernel descent of the identity on the ideal. -/
theorem firstOrderQuotientInv_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderQuotientInv i =
      cokernel.desc
        (Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i))
        (𝟙 (Hom.idealSheaf i)) (firstOrderIdealAction_comp_id i) :=
  rfl

/-- The module inclusion `I/I² ⟶ 𝒪` of a first-order thickening. -/
def firstOrderIdealIncl {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  firstOrderQuotientInv i ≫ Hom.idealSheafι i

/-- The conormal quotient inclusion is the quotient inverse followed by the ideal inclusion. -/
theorem firstOrderIdealIncl_eq {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsFirstOrderThickening i] :
    firstOrderIdealIncl i = firstOrderQuotientInv i ≫ Hom.idealSheafι i :=
  rfl

/-- Naturality of the objectwise additive maps underlying a relative derivation. -/
theorem derivationAdditiveMap_naturality {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : Hom.derivations sY F)
    {U V : (smallEtaleSite Y)ᵒᵖ} (g : U ⟶ V) :
    ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y)).obj.map g ≫ AddCommGrpCat.ofHom D.d =
      AddCommGrpCat.ofHom D.d ≫
        ((SheafOfModules.toSheaf (structureSheaf Y)).obj F).obj.map g :=
  sorry

/-- The underlying presheaf morphism of a relative derivation, assembled from `D.d`. -/
def derivationAdditiveMap_presheaf {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : Hom.derivations sY F) :
    ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y)).obj ⟶
      ((SheafOfModules.toSheaf (structureSheaf Y)).obj F).obj :=
  { app := fun _ ↦ AddCommGrpCat.ofHom D.d
    naturality := fun _ _ g ↦ derivationAdditiveMap_naturality sY F D g }

/-- The underlying natural transformation has the sectionwise additive maps of the derivation as components. -/
theorem derivationAdditiveMap_presheaf_eq {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : Hom.derivations sY F) :
    derivationAdditiveMap_presheaf sY F D =
      { app := fun _ ↦ AddCommGrpCat.ofHom D.d
        naturality := fun _ _ g ↦ derivationAdditiveMap_naturality sY F D g } :=
  rfl

/-- The additive sheaf morphism `𝒪_Y ⟶ F` induced by the objectwise maps `D.d`. -/
def derivationAdditiveMap {Y B : AlgebraicSpace S} (sY : Y ⟶ B) (F : Y.Modules)
    (D : Hom.derivations sY F) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y) ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj F :=
  InducedCategory.homMk (derivationAdditiveMap_presheaf sY F D)

/-- The additive sheaf map is induced by the sectionwise maps of the derivation. -/
theorem derivationAdditiveMap_eq {Y B : AlgebraicSpace S} (sY : Y ⟶ B)
    (F : Y.Modules) (D : Hom.derivations sY F) :
    derivationAdditiveMap sY F D =
      InducedCategory.homMk (derivationAdditiveMap_presheaf sY F D) :=
  rfl

/-- Inverse image of `iY^♯ : 𝒪_{Y'} ⟶ 𝒪_Y` along `a`, on `X_spaces,étale`. -/
def inverseImageRestriction {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    inverseImageClosedStructureSheaf a iY ⟶
      (spacesRingedToposHom a).toTopos.ringInverseImage.obj (spacesStructureSheaf Y) :=
  (spacesRingedToposHom a).toTopos.ringInverseImage.map
    (closedStructureSheaf_structureMap iY)

/-- The pulled restriction is the ring inverse image of the closed structure-sheaf map. -/
theorem inverseImageRestriction_eq {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y)
    (iY : Y ⟶ Y') :
    inverseImageRestriction a iY =
      (spacesRingedToposHom a).toTopos.ringInverseImage.map
        (closedStructureSheaf_structureMap iY) :=
  rfl

/-- Restriction `𝒪_{Y'} ⟶ 𝒪_Y` pulled to `X_étale`. -/
def pulledRestriction {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj
          ((spacesRingedToposHom a).toTopos.ringInverseImage.obj
            (spacesStructureSheaf Y))) :=
  (EtaleAdditive.restriction X).map ((forgetSpacesRing X).map (inverseImageRestriction a iY))

/-- The small étale restriction map is the restriction of the additive inverse-image map. -/
theorem pulledRestriction_eq {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    pulledRestriction a iY =
      (EtaleAdditive.restriction X).map
        ((forgetSpacesRing X).map (inverseImageRestriction a iY)) :=
  rfl

/-- Inverse image of the additive sheaf map induced by `D.d`. -/
def pulledDerivation {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : Hom.derivations sY ((Modules.pushforward a).obj F)) :
    (EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) ⟶
      (EtaleAdditive.inverseImage a).obj
        ((SheafOfModules.toSheaf (structureSheaf Y)).obj
          ((Modules.pushforward a).obj F)) :=
  (EtaleAdditive.inverseImage a).map
    (derivationAdditiveMap sY ((Modules.pushforward a).obj F) D)

/-- The pulled derivation is the additive inverse image of its underlying sheaf map. -/
theorem pulledDerivation_eq {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : Hom.derivations sY ((Modules.pushforward a).obj F)) :
    pulledDerivation sY a D =
      (EtaleAdditive.inverseImage a).map
        (derivationAdditiveMap sY ((Modules.pushforward a).obj F) D) :=
  rfl

/-- The adjunct of `D.d`, as an abelian sheaf map `a⁻¹ 𝒪_Y ⟶ C` on `X_étale`. -/
def derivationAdjunct {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : Hom.derivations sY ((Modules.pushforward a).obj F)) :
    (EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj F :=
  pulledDerivation sY a D ≫
    (EtaleAdditive.inverseImage a).map (modulePushforwardForgetAdd a F) ≫
    (EtaleAdditive.adjunction a).counit.app
      ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- The adjunct of a derivation is its inverse image followed by the direct-image comparison and counit. -/
theorem derivationAdjunct_eq {X Y B : AlgebraicSpace S} (sY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (D : Hom.derivations sY ((Modules.pushforward a).obj F)) :
    derivationAdjunct sY a D =
      pulledDerivation sY a D ≫
        (EtaleAdditive.inverseImage a).map (modulePushforwardForgetAdd a F) ≫
        (EtaleAdditive.adjunction a).counit.app
          ((SheafOfModules.toSheaf (structureSheaf X)).obj F) :=
  rfl

/-- Identify the pushed-forward conormal with its supported quotient using the actual
coborder and module-unit inverse section maps. -/
def pushforwardConormalToQuotient {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (Modules.pushforward i).obj (Hom.conormalSheaf i) ⟶
      Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i) :=
  (Modules.pushforward i).map (pullbackQuotientToConormalInv i) ≫
    conormalQuotientUnitInv i

/-- The supported quotient comparison recovers the canonical quotient-to-conormal map. -/
@[simp]
theorem unit_map_comp_pushforwardConormalToQuotient {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFirstOrderThickening i] :
    (Modules.pullbackPushforwardAdjunction i).unit.app
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
      (Modules.pushforward i).map (pullbackQuotientToConormal i) ≫
      pushforwardConormalToQuotient i = 𝟙 _ := sorry

/-- The canonical quotient-to-conormal map recovers every pushed-forward conormal section. -/
@[simp]
theorem pushforwardConormalToQuotient_comp_unit_map {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFirstOrderThickening i] :
    pushforwardConormalToQuotient i ≫
      (Modules.pullbackPushforwardAdjunction i).unit.app
        (Modules.quotientByIdeal (Hom.idealSheafSubobject i) (Hom.idealSheaf i)) ≫
      (Modules.pushforward i).map (pullbackQuotientToConormal i) = 𝟙 _ := sorry

/-- The additive map `i_* C_{X/X'} ⟶ 𝒪_{X'}` obtained from `I/I² ⟶ 𝒪` after
identifying `i_* C` with `I/I²`. -/
def pushforwardConormalToStructure {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (EtaleAdditive.directImage i).obj
        ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ⟶
      (sheafCompose (smallEtaleTopology X') (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf X') :=
  modulePushforwardForgetAddInv i (Hom.conormalSheaf i) ≫
    (SheafOfModules.toSheaf (structureSheaf X')).map (pushforwardConormalToQuotient i) ≫
    (SheafOfModules.toSheaf (structureSheaf X')).map (firstOrderIdealIncl i) ≫
    (unitToForgetAddIso X').hom

/-- The supported conormal inclusion is the quotient comparison followed by the first-order ideal inclusion. -/
theorem pushforwardConormalToStructure_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    pushforwardConormalToStructure i =
      modulePushforwardForgetAddInv i (Hom.conormalSheaf i) ≫
        (SheafOfModules.toSheaf (structureSheaf X')).map (pushforwardConormalToQuotient i) ≫
        (SheafOfModules.toSheaf (structureSheaf X')).map (firstOrderIdealIncl i) ≫
        (unitToForgetAddIso X').hom :=
  rfl

/-- The comparison `F ⟶ i^{-1} i_* F` on a first-order thickening. -/
def toInverseImagePushforward {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    F ⟶ (EtaleAdditive.inverseImage i).obj ((EtaleAdditive.directImage i).obj F) :=
  (EtaleAdditive.Thickening.counitIso i F).inv

/-- The map into inverse image of direct image is the explicit inverse of the thickening counit. -/
theorem toInverseImagePushforward_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    toInverseImagePushforward i F =
      (EtaleAdditive.Thickening.counitIso i F).inv :=
  rfl

/-- The original counit followed by the comparison is the identity. -/
theorem counit_toInverseImagePushforward {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (EtaleAdditive.adjunction i).counit.app F ≫ toInverseImagePushforward i F = 𝟙 _ :=
  (EtaleAdditive.Thickening.counitIso i F).hom_inv_id

/-- The comparison followed by the original counit is the identity. -/
theorem toInverseImagePushforward_counit {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    toInverseImagePushforward i F ≫ (EtaleAdditive.adjunction i).counit.app F = 𝟙 F :=
  (EtaleAdditive.Thickening.counitIso i F).inv_hom_id

/-- The inclusion `C_{X/X'} ⟶ i^{-1} 𝒪_{X'}` of a first-order thickening, obtained
as the geometric inverse image of `I/I² ⟶ 𝒪` after the forgetful comparison
`i_* C ⟶ I/I²` that does not extend scalars. -/
def conormalInclusion {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf i)) :=
  toInverseImagePushforward i
      ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ≫
    (EtaleAdditive.inverseImage i).map (pushforwardConormalToStructure i) ≫
    (restrictInverseImageIso i).inv

/-- The conormal inclusion is the inverse counit followed by the inverse image of the supported inclusion and site comparison. -/
theorem conormalInclusion_eq {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    conormalInclusion i =
      toInverseImagePushforward i
          ((SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i)) ≫
        (EtaleAdditive.inverseImage i).map (pushforwardConormalToStructure i) ≫
        (restrictInverseImageIso i).inv :=
  rfl

/-- The composite `𝒪_{Y'} ⟶ 𝒪_Y ⟶^D a_* C_{X/X'} ⟶ a_* 𝒪_{X'}`,
transported to the hom-type of `structureMapDifference_restrict`. -/
def factorizationMap {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))) :
    (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf iX)) :=
  pulledRestriction a iY ≫
    (restrictInverseImageIso a).hom ≫
    derivationAdjunct sY a D ≫
    conormalInclusion iX

/-- The factorization is the restriction followed by the site comparison, derivation adjunct and conormal inclusion. -/
theorem factorizationMap_eq {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))) :
    factorizationMap sY iX iY a D =
      pulledRestriction a iY ≫
        (restrictInverseImageIso a).hom ≫
        derivationAdjunct sY a D ≫
        conormalInclusion iX :=
  rfl

/-- Sectionwise values of the transported composite through `D.d` and
`conormalInclusion`. -/
def factorizationMap_apply {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    ((EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (closedStructureSheaf iX))).obj.obj V :=
  ConcreteCategory.hom ((factorizationMap sY iX iY a D).hom.app V) x

/-- Section evaluation of the factorization is evaluation of its additive sheaf morphism. -/
theorem factorizationMap_apply_eq {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    factorizationMap_apply sY iX iY a D V x =
      ConcreteCategory.hom ((factorizationMap sY iX iY a D).hom.app V) x :=
  rfl

/-- A witness derivation recovers the inverse-image difference of `(a')^♯` and
`(b')^♯` as the composite through `D.d` and `conormalInclusion`. -/
theorem exists_differenceDerivation_spec {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB)
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))
    (hD : structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
      factorizationMap sY iX iY a D)
    (V : (smallEtaleSite X)ᵒᵖ)
    (x : ((EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))).obj.obj V) :
    ConcreteCategory.hom
        ((structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm).hom.app V) x =
      ConcreteCategory.hom ((conormalInclusion iX).hom.app V)
        (ConcreteCategory.hom ((derivationAdjunct sY a D).hom.app V)
          (ConcreteCategory.hom ((restrictInverseImageIso a).hom.hom.app V)
            (ConcreteCategory.hom ((pulledRestriction a iY).hom.app V) x))) :=
  sorry

/-- The additive sheaf of the actual source conormal module. -/
abbrev differenceCoefficient {X X' : AlgebraicSpace S} (iX : X ⟶ X')
    [IsFirstOrderThickening iX] :=
  (SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf iX)

/-- The first-order conormal inclusion is injective on every actual section object. -/
theorem conormalInclusion_app_injective {X X' : AlgebraicSpace S} (iX : X ⟶ X')
    [IsFirstOrderThickening iX] (U : (smallEtaleSite X)ᵒᵖ) :
    Function.Injective (fun m : (differenceCoefficient iX).obj.obj U ↦
      (conormalInclusion iX).hom.app U m) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
