module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.InverseImageStalk

/-!
# Étale local-ring maps induced by morphisms of algebraic spaces
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

/-- Canonical identification of `𝒪_{Y, ȳ}` with the stalk of `f⁻¹ 𝒪_Y` at `x̄`, as types. -/
def inverseImageStructureSheafStalkTypeIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    (forget RingCat.{u}).obj
        (((toSmallEtalePoint (xbar.map f)).presheafFiber).obj (structureSheaf Y).obj) ≅
      (forget RingCat.{u}).obj (inverseImageEtaleLocalRingCat f xbar) :=
  (forgetRingSheaf_stalkIso (xbar.map f) (structureSheaf Y)).symm ≪≫
    Equiv.toIso
      { toFun :=
          (typeInverseImageStalkInv f xbar).app (forgetRingSheaf (structureSheaf Y))
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

end AlgebraicGeometry.AlgebraicSpace
