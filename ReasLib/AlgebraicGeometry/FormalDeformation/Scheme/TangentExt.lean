/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.DualNumber.Ideal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.FlatLift.Classification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import Mathlib.Algebra.Homology.Single

/-! # Infinitesimal automorphisms and tangent classes of schemes via cotangent extensions -/

@[expose] public section

-- Local declaration justification (module visibility): the explicit comparisons and
-- their types use private coefficient transport and underlying-map definitions.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber ArtinianLocalAlgCat
open AlgebraicGeometry.Scheme.Thickening
open AlgebraicGeometry.Scheme.Thickening.FlatLift
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- The trivial dual-number lift of `X` in the slice `Def_X`. -/
def trivialLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    (deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X hX).obj (Over.mk
        (retraction (forget Λ k) (trivialPushforward Λ k X hX))) =
      dualNumber Λ k)

/-- The zero tangent vector of `Def_X`. -/
def trivialTangent (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) : tangentSpace Λ k X hX :=
  Functor.tangentSpaceAt.mk (forget Λ k) (residueObj Λ k X hX) (trivialLift Λ k X hX)

/-- The dual-number closed immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_dualNumberToResidue :
    AlgebraicGeometry.IsFirstOrderThickening (X := Spec (CommRingCat.of k))
      (specMap (dualNumberToResidue Λ k)) := sorry

/-- The trivial dual-number lift of `hX` as a flat first-order thickening lift. -/
def trivialFlatLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    FlatLift (S := Spec (CommRingCat.of k))
      (specMap (dualNumberToResidue Λ k)) hX :=
  FlatLift.of (trivialSchemeOver Λ k X hX) (trivialSchemeImmersion Λ k X hX) sorry

/-- Identification `f^* 𝒞_{Spec k / Spec k[ε]} ≅ 𝒪_X` for the trivial dual-number
thickening, via the ε-coefficient isomorphism `ker(k[ε] → k) ≅ k`. -/
def pulledConormalUnitIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    pulledConormal (S := Spec (CommRingCat.of k))
      (specMap (dualNumberToResidue Λ k)) hX ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (hX.toShHom ^*).mapIso
      (conormalIdealIso (Y := Spec (CommRingCat.of k)) (specMap (dualNumberToResidue Λ k))) ≪≫
    (hX.toShHom ^*).mapIso (residueKernelIsoUnit Λ k) ≪≫
    (hX.toShHom ^*).mapIso
      (unitIsoTensorUnit
        (Spec (CommRingCat.of k)).toRingedSpace) ≪≫
    pullbackUnitIso hX.toShHom ≪≫
    (unitIsoTensorUnit X.toRingedSpace).symm

/-- Ext⁰ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extZero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :=
  Ext⁽(0 : ℤ)⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[hX.toShHom],
    (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Ext¹ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extOne (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :=
  Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[hX.toShHom],
    (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Postcomposition transports cotangent extensions along a morphism of coefficient modules. -/
private def extNLMap (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (n : ℤ)
    {F G : X.toRingedSpace.Modules} (φ : F ⟶ G) :
    Ext⁽n⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[hX.toShHom],
        (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj F)) →
      Ext⁽n⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[hX.toShHom],
        (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj G)) :=
  fun ξ ↦ ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) n).map
    ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map φ))

/-- Transport Ext⁰ of `f^* 𝒞` to Ext⁰ of `𝒪_X`. -/
private def extZeroOfNL (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (ξ : extZeroNL (S := Spec (CommRingCat.of k)) (specMap (dualNumberToResidue Λ k)) hX) :
    extZero k X hX :=
  extNLMap k X hX (0 : ℤ) (pulledConormalUnitIso Λ k X hX).hom ξ

/-- Transport Ext¹ of `𝒪_X` to Ext¹ of `f^* 𝒞`. -/
private def extOneNLOf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (ξ : extOne k X hX) :
    extOneNL (S := Spec (CommRingCat.of k)) (specMap (dualNumberToResidue Λ k)) hX :=
  extNLMap k X hX (1 : ℤ) (pulledConormalUnitIso Λ k X hX).inv ξ

/-- The scheme automorphism of `X'` underlying an infinitesimal automorphism of `X`. -/
private def infSchemeHom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (α : inf Λ k X hX) :
    trivialScheme Λ k X hX ⟶ trivialScheme Λ k X hX :=
  (fiberInclusion.map α.val.hom).schemeHom

/-- Automorphisms of the trivial lift reducing to the identity on `X`, from `Inf(Def_X)`. -/
def infToReduceIdAuto (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (α : inf Λ k X hX) :
    ReduceIdAuto (trivialFlatLift Λ k X hX) :=
  let hom := infSchemeHom Λ k X hX α
  let laws : (hom ≫ (trivialFlatLift Λ k X hX).f' =
      (trivialFlatLift Λ k X hX).f') ∧
      ((trivialFlatLift Λ k X hX).i ≫ hom = (trivialFlatLift Λ k X hX).i) ∧
      IsIso hom := sorry
  { hom := hom
    over := laws.1
    restrict := laws.2.1
    isIso := laws.2.2 }

/-- The comparison `Inf(Def_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`. -/
def infToExtZero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    inf Λ k X hX → extZero k X hX :=
  fun α ↦ extZeroOfNL Λ k X hX
    (reduceIdAutoEquiv (trivialFlatLift Λ k X hX) (infToReduceIdAuto Λ k X hX α))

/-- `infToExtZero` is `reduceIdAutoEquiv` of `infToReduceIdAuto`, transported to `𝒪_X`. -/
theorem infToExtZero_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (α : inf Λ k X hX) :
    infToExtZero Λ k X hX α =
      extZeroOfNL Λ k X hX
        (reduceIdAutoEquiv (trivialFlatLift Λ k X hX) (infToReduceIdAuto Λ k X hX α)) := rfl

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`,
induced by degree-zero homology of the naive cotangent complex. -/
def extZeroToHomOmegaOfUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (ξ : extZero k X hX) :
    (Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :=
  (RingedSpace.NaiveCotangent.homologyZeroIso hX.toShHom).inv ≫
    (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (0 : ℤ)).inv.app
      NL[hX.toShHom] ≫
    (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (0 : ℤ)).map
      ((CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        X.toRingedSpace.Modules (0 : ℤ)).hom.app
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`,
via the canonical augmentation of `NL_{X/k}` and the degree-zero Ext chart. -/
def homOmegaToExtZeroOfUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (α : Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :
    extZero k X hX :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
      (RingedSpace.NaiveCotangent.augmentation hX.toShHom ≫
        (CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map α) ≫
      (DerivedCategory.singleFunctorIsoCompQ X.toRingedSpace.Modules (0 : ℤ)).hom.app
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`. -/
def extZeroEquivHomOmega (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    extZero k X hX ≃ (Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :=
  let forward := extZeroToHomOmegaOfUnit k X hX
  let backward := homOmegaToExtZeroOfUnit k X hX
  let laws : Function.LeftInverse backward forward ∧
      Function.RightInverse backward forward := sorry
  { toFun := forward
    invFun := backward
    left_inv := laws.1
    right_inv := laws.2 }

/-- `extZeroEquivHomOmega` sends an Ext⁰ class to the corresponding map out of `Ω_{X/k}`. -/
theorem extZeroEquivHomOmega_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (ξ : extZero k X hX) :
    extZeroEquivHomOmega k X hX ξ = extZeroToHomOmegaOfUnit k X hX ξ := rfl

/-- The dual-number fibre object of `Def_X` associated to a flat first-order lift. -/
def ofFlatLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (L : FlatLift (S := Spec (CommRingCat.of k)) (specMap (dualNumberToResidue Λ k)) hX) :
    (deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X hX).obj
        (Over.mk
          (Hom.of (dualNumberToResidue Λ k) L.i L.isPullback.flip :
            of (dualNumber Λ k) L.space L.f' L.flat ⟶
              fiberInclusion.obj (residueObj Λ k X hX))) =
      dualNumber Λ k)

/-- Isomorphism classes of flat lifts map to tangent vectors of `Def_X`. -/
def ofIsoClass (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    IsoClass (S := Spec (CommRingCat.of k))
      (specMap (dualNumberToResidue Λ k)) hX → tangentSpace Λ k X hX :=
  Quotient.lift
    (fun L ↦ Functor.tangentSpaceAt.mk (forget Λ k) (residueObj Λ k X hX)
      (ofFlatLift Λ k X hX L)) sorry

/-- The class of a lift is sent to the class of `ofFlatLift`. -/
theorem ofIsoClass_mk (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k))
    (L : FlatLift (S := Spec (CommRingCat.of k)) (specMap (dualNumberToResidue Λ k)) hX) :
    ofIsoClass Λ k X hX (Quotient.mk _ L) =
      Functor.tangentSpaceAt.mk (forget Λ k) (residueObj Λ k X hX) (ofFlatLift Λ k X hX L) := rfl

/-- The comparison `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ T Def_X`. -/
def ofExtOne (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    extOne k X hX → tangentSpace Λ k X hX :=
  fun ξ ↦ ofIsoClass Λ k X hX
    (isoClassEquiv (trivialFlatLift Λ k X hX) (extOneNLOf Λ k X hX ξ))

/-- `ofExtOne` sends an Ext¹ class to the translate of the trivial lift. -/
theorem ofExtOne_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) (ξ : extOne k X hX) :
    ofExtOne Λ k X hX ξ =
      ofIsoClass Λ k X hX
        (isoClassEquiv (trivialFlatLift Λ k X hX) (extOneNLOf Λ k X hX ξ)) := rfl

/-- The zero Ext¹ class is sent to the trivial tangent vector. -/
theorem ofExtOne_zero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    ofExtOne Λ k X hX 0 = trivialTangent Λ k X hX := sorry

/-- Infinitesimal automorphisms of a scheme are classified by degree-zero extensions
of its naive cotangent complex by its structure module. -/
theorem infToExtZero_bijective (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    Function.Bijective (infToExtZero Λ k X hX) := sorry

/-- Dual-number deformation classes of a scheme are classified by degree-one extensions
of its naive cotangent complex by its structure module. -/
theorem ofExtOne_bijective (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    Function.Bijective (ofExtOne Λ k X hX) := sorry

end FlatSchemeCat
