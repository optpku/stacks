/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsFirstOrderThickening i]

/-- The inverse-image presentation sheaf of a first-order thickening, as the
universe lift of `i⁻¹𝒪_{X'}` to `CommRingCat.{u + 1}` on `X_étale`. -/
def presentationSheaf : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X)
      CommRingCat.universeLift.{u, u + 1}).obj (commInverseImageStructureSheaf i)

/-- The underlying presheaf of `presentationSheaf i` is the universe lift of
`i⁻¹𝒪_{X'}`. -/
theorem presentationSheaf_obj :
    (presentationSheaf i).obj =
      (commInverseImageStructureSheaf i).obj ⋙ CommRingCat.universeLift.{u, u + 1} :=
  rfl

/-- The canonical projection `i⁻¹𝒪_{X'} ⟶ 𝒪_X` on `X_étale`, after universe
lift. -/
def presentationProjection : presentationSheaf i ⟶ commStructureSheafLift X :=
  (sheafCompose (smallEtaleTopology X)
        CommRingCat.universeLift.{u, u + 1}).map
      (commInverseImageStructureSheafMap i) ≫
    (commStructureSheafComposeLiftIso X).hom

/-- The kernel of the inverse-image presentation of a first-order thickening is
square zero. -/
theorem presentationKernel_isSquareZero :
    KernelIdeal.IsSquareZero (presentationProjection i) := sorry

/-- The inverse-image presentation projection of a first-order thickening is
locally surjective. -/
instance presentationProjection_isLocallySurjective :
    Sheaf.IsLocallySurjective (presentationProjection i) := sorry

/-- The inverse-image presentation sheaf of a first-order thickening is locally
ringed. -/
instance presentationSheaf_isLocallyRinged :
    (presentationSheaf i).IsLocallyRinged := sorry

/-- The kernel of the presentation projection, as an additive sheaf on
`X_étale`. This is the coefficient sheaf `I` in the Picard cohomology
sequence. -/
abbrev presentationKernelAdditive :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  KernelIdeal.underlyingAdditive.{u + 1, u, u + 1} (presentationProjection i)

/-- The additive sheaf underlying the inverse-image presentation, before universe
lift. -/
def inverseImageAdditive :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
    (commInverseImageStructureSheaf i)

/-- The additive sheaf underlying `𝒪_X` on `X_étale`. -/
def structureAdditive :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
    (commStructureSheaf X)

/-- The additive map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` on `X_étale`. -/
def inverseImageAdditiveMap :
    inverseImageAdditive i ⟶ structureAdditive :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u})).map
    (commInverseImageStructureSheafMap i)

/-- The pulled associated ideal-sheaf map, after universe lift of the additive
inverse-image presentation. -/
def pulledIdealSheafMap :
    (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (inverseImageAdditive i) ⟶
      (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (structureAdditive) :=
  (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (inverseImageAdditiveMap i)

/-- The additive sheaf of the associated ideal sheaf of `i` on `X_étale`, as the
kernel of the additive inverse-image map `i⁻¹𝒪_{X'} ⟶ 𝒪_X` after universe lift.
This is the source coefficient `I` in the Picard cohomology sequence. -/
def pulledIdealSheafAdditive :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  kernel (pulledIdealSheafMap i)

/-- The presentation kernel is the categorical kernel of the underlying additive
map of `presentationProjection i`. -/
def presentationKernelAdditiveKernelIso :=
  KernelIdeal.underlyingKernelIso.{u + 1, u, u + 1} (presentationProjection i)

/-- The additive sheaf of the universe-lifted inverse-image presentation. -/
def presentationUnitForget :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (presentationSheaf i)

/-- Identifying the unit of the inverse-image presentation with its underlying
additive sheaf, by fully faithful reflection of the identity on presheaves. -/
def presentationUnitForgetIso :
    KernelIdeal.underlyingUnit.{u + 1, u, u + 1} (presentationSheaf i) ≅
      presentationUnitForget i :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
    (Iso.refl _)

/-- Universe lift of the unlifted additive inverse-image sheaf. -/
def inverseImageAdditiveLift :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (inverseImageAdditive i)

/-- Identifying the additive sheaf of the lifted presentation with the universe
lift of the unlifted additive inverse-image sheaf. -/
def presentationUnitLiftIso :
    presentationUnitForget i ≅ inverseImageAdditiveLift i :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
    (isoWhiskerLeft (commInverseImageStructureSheaf i).obj CommRingCat.universeLiftForgetAddIso)

/-- Additive identification of the universe-lifted unit of the inverse-image
presentation with the universe lift of the additive sheaf of `i⁻¹𝒪_{X'}`. -/
def presentationUnitIsoPulledDomain :
    KernelIdeal.underlyingUnit.{u + 1, u, u + 1} (presentationSheaf i) ≅
      (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (inverseImageAdditive i) :=
  presentationUnitForgetIso i ≪≫ presentationUnitLiftIso i

/-- The additive sheaf of the universe-lifted structure sheaf of `X`. -/
def presentationTargetForget :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (commStructureSheafLift X)

/-- Identifying the presentation target with the additive sheaf of the lifted
structure sheaf, by fully faithful reflection of the identity on presheaves. -/
def presentationTargetForgetIso :
    KernelIdeal.underlyingTarget.{u + 1, u, u + 1} (presentationProjection i) ≅
      presentationTargetForget :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
    (Iso.refl _)

/-- Universe lift of the unlifted additive structure sheaf of `X`. -/
def structureAdditiveLift :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (structureAdditive)

/-- Identifying the additive sheaf of the lifted structure sheaf with the
universe lift of the unlifted additive structure sheaf. -/
def presentationTargetLiftIso :
    presentationTargetForget (X := X) ≅ structureAdditiveLift (X := X) :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
    (isoWhiskerLeft (commStructureSheaf X).obj CommRingCat.universeLiftForgetAddIso)

/-- Additive identification of the presentation target with the universe lift of
the additive sheaf of `𝒪_X`. -/
def presentationTargetIsoPulledCodomain :
    KernelIdeal.underlyingTarget.{u + 1, u, u + 1} (presentationProjection i) ≅
      (sheafCompose (smallEtaleTopology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (structureAdditive) :=
  presentationTargetForgetIso i ≪≫ presentationTargetLiftIso

/-- The presentation kernel identifies with the kernel of the additive
inverse-image map after universe lift. -/
def idealSheafComparison :
    presentationKernelAdditive i ≅ pulledIdealSheafAdditive i :=
  presentationKernelAdditiveKernelIso i ≪≫
    kernel.mapIso
      (KernelIdeal.underlyingProjection.{u + 1, u, u + 1} (presentationProjection i))
      (pulledIdealSheafMap i) (presentationUnitIsoPulledDomain i)
      (presentationTargetIsoPulledCodomain i) sorry

/-- Degree-`n` cohomology of the presentation kernel is identified with
cohomology of the pulled associated ideal sheaf. -/
def presentationKernelAdditive_H_equiv (n : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})] :
    (presentationKernelAdditive i).H n ≃+ (pulledIdealSheafAdditive i).H n where
  toFun := Sheaf.H.map (idealSheafComparison i).hom n
  invFun := Sheaf.H.map (idealSheafComparison i).inv n
  left_inv := sorry
  right_inv := sorry
  map_add' := (Sheaf.H.map (idealSheafComparison i).hom n).map_add

/-- The forward map of `presentationKernelAdditive_H_equiv` is cohomology of
`idealSheafComparison i`. -/
theorem presentationKernelAdditive_H_equiv_apply (n : ℕ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (x : (presentationKernelAdditive i).H n) :
    presentationKernelAdditive_H_equiv i n x =
      Sheaf.H.map (idealSheafComparison i).hom n x :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
