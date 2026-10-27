/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.Conormal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.ExtZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Thickening
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening
namespace FlatLift

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- The identity filling of the identity cube has commuting square `L.i ≫ 𝟙 = 𝟙 ≫ L.i`. -/
theorem id_comm_thickening (L : FlatLift t f) :
    L.i ≫ 𝟙 L.space = 𝟙 X ≫ L.i := sorry

/-- The identity algebra map of a flat lift, as `(𝟙_{X'})^♯` on `X_spaces,étale`. -/
def idAlgebraMap (L : FlatLift t f) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  structureMap_transported L.i L.i (𝟙 X) (𝟙 L.space) (id_comm_thickening L)

/-- A reducing-to-identity automorphism fills the identity cube. -/
theorem autoAlgebraMap_comm_thickening {L : FlatLift t f} (φ : ReduceIdAuto L) :
    L.i ≫ φ.hom = 𝟙 X ≫ L.i := sorry

/-- Identity-cube algebra map of a reducing-to-identity automorphism. -/
def autoAlgebraMap {L : FlatLift t f} (φ : ReduceIdAuto L) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  structureMap_transported L.i L.i (𝟙 X) φ.hom (autoAlgebraMap_comm_thickening φ)

/-- The identity filling commutes with the structure-sheaf square. -/
theorem idAlgebraMap_commutes (L : FlatLift t f) :
    structureMap_commutes L.i L.i (𝟙 X) (idAlgebraMap L) := sorry

/-- The identity filling is an `𝒪_{Y'}`-algebra map. -/
theorem idAlgebraMap_isAlgebra (L : FlatLift t f) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) (idAlgebraMap L) :=
  sorry

/-- The identity-cube algebra map of a reducing-to-identity automorphism commutes
with the structure-sheaf square. -/
theorem autoAlgebraMap_commutes {L : FlatLift t f} (φ : ReduceIdAuto L) :
    structureMap_commutes L.i L.i (𝟙 X) (autoAlgebraMap φ) := sorry

/-- The identity-cube algebra map of a reducing-to-identity automorphism is an
`𝒪_{Y'}`-algebra map. -/
theorem autoAlgebraMap_isAlgebra {L : FlatLift t f} (φ : ReduceIdAuto L) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) (autoAlgebraMap φ) :=
  sorry

/-- The inverse-image form of `α - (𝟙_{X'})^♯` on `X_spaces,étale`. -/
def algebraMapAddDiff {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i) :
    (Hom.Deformation.forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i) ⟶
      (Hom.Deformation.forgetSpacesRing X).obj (closedStructureSheaf L.i) :=
  (Hom.Deformation.forgetSpacesRing X).map α - (Hom.Deformation.forgetSpacesRing X).map (idAlgebraMap L)

/-- `algebraMapAddDiff` is the additive difference of `α` and the identity filling. -/
theorem algebraMapAddDiff_eq {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i) :
    algebraMapAddDiff α =
      (Hom.Deformation.forgetSpacesRing X).map α - (Hom.Deformation.forgetSpacesRing X).map (idAlgebraMap L) :=
  rfl

/-- Factorization of `α - id` through `Ker(i^♯)`. -/
def algebraMapDiffKernel {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) :
    (Hom.Deformation.forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i) ⟶
      kernel ((Hom.Deformation.forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)) :=
  kernel.lift ((Hom.Deformation.forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i))
    (algebraMapAddDiff α) sorry

/-- `algebraMapDiffKernel` is the kernel lift of `algebraMapAddDiff`. -/
theorem algebraMapDiffKernel_eq {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) :
    algebraMapDiffKernel α hα ≫
      kernel.ι ((Hom.Deformation.forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)) =
      algebraMapAddDiff α :=
  sorry

/-- The identity-cube universal derivation `i^{-1} 𝒪_{X'} ⟶ Ω[f]` on `X_étale`. -/
def structureDerivation (L : FlatLift t f) :
    (EtaleAdditive.restriction X).obj
        ((Hom.Deformation.forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i)) ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj Ω[f] :=
  (EtaleAdditive.restriction X).map ((Hom.Deformation.forgetSpacesRing X).map
      (idAlgebraMap L ≫ closedStructureSheaf_structureMap L.i)) ≫
    (((EtaleAdditive.continuousComposeIso (smallEtaleToSpaces X)
      (forget₂ RingCat AddCommGrpCat.{u}) (smallEtaleTopology X)
      (spacesEtaleTopology X)).symm.app (spacesStructureSheaf X))).hom ≫
    (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).map
      ((EtaleRingedTopos.ringExtensionRestrictionIso X).hom.app (structureSheaf X)) ≫
    Hom.Deformation.derivationAdditiveMap f (Ω[f]) (Hom.universalDerivation f)

/-- Postcomposition with `structureDerivation L` is injective on `Hom(Ω[f], f^* 𝒞)`. -/
theorem structureDerivation_injective (L : FlatLift t f) :
    Function.Injective
      (fun θ : Ω[f] ⟶ pulledConormal t f ↦
        structureDerivation L ≫
          (SheafOfModules.toSheaf (structureSheaf X)).map θ) := sorry

/-- `θ : Ω[f] ⟶ f^* 𝒞` classifies the identity-cube difference `α - id` when it
recovers that difference under `Ker(i^♯) ≅ f^* 𝒞`. -/
def classifiesDifference {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) (θ : Ω[f] ⟶ pulledConormal t f) : Prop :=
  structureDerivation L ≫ (SheafOfModules.toSheaf (structureSheaf X)).map θ =
    (EtaleAdditive.restriction X).map (algebraMapDiffKernel α hα) ≫
      (CanonicalKernel.iso L).hom

/-- Unfolding of `classifiesDifference`. -/
theorem classifiesDifference_iff {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) (θ : Ω[f] ⟶ pulledConormal t f) :
    classifiesDifference α hα θ ↔
      structureDerivation L ≫ (SheafOfModules.toSheaf (structureSheaf X)).map θ =
        (EtaleAdditive.restriction X).map (algebraMapDiffKernel α hα) ≫
          (CanonicalKernel.iso L).hom := sorry

/-- Unique factorization of `α - id` through `Ω[f]`. -/
theorem existsUnique_derivationOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    ExistsUnique fun θ : Ω[f] ⟶ pulledConormal t f ↦ classifiesDifference α hα θ :=
  sorry

/-- The identity-cube derivation of an algebra map `α`, as the unique map
`Ω[f] ⟶ f^* 𝒞` classifying `α - id` under `Ker(i^♯) ≅ f^* 𝒞`. -/
def derivationOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    (Ω[f] ⟶ pulledConormal t f) :=
  Classical.choose (existsUnique_derivationOfAlgebraMap α hα halg)

/-- The selected derivation recovers the additive difference from the identity filling. -/
theorem derivationOfAlgebraMap_classifies {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    classifiesDifference α hα (derivationOfAlgebraMap α hα halg) :=
  (Classical.choose_spec (existsUnique_derivationOfAlgebraMap α hα halg)).1

/-- Any derivation recovering the specified algebra-map difference is the selected derivation. -/
theorem derivationOfAlgebraMap_unique {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α)
    (θ : Ω[f] ⟶ pulledConormal t f) (hθ : classifiesDifference α hα θ) :
    θ = derivationOfAlgebraMap α hα halg :=
  (Classical.choose_spec (existsUnique_derivationOfAlgebraMap α hα halg)).2 θ hθ

/-- `derivationOfAlgebraMap α` vanishes iff `α` is the identity filling. -/
theorem derivationOfAlgebraMap_spec {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    derivationOfAlgebraMap α hα halg = 0 ↔ α = idAlgebraMap L := sorry

/-- The Ext⁰ class of an identity-cube algebra map, via `Hom(Ω[f], f^* 𝒞) ≃ Ext⁰`. -/
def extZeroOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    extZeroNL t f :=
  Hom.NaiveCotangent.homToExtZero f (derivationOfAlgebraMap α hα halg)

/-- `extZeroOfAlgebraMap` is `Hom.NaiveCotangent.homToExtZero f` of the identity-cube derivation of `α`. -/
theorem extZeroOfAlgebraMap_spec {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    extZeroOfAlgebraMap α hα halg =
      Hom.NaiveCotangent.homToExtZero f (derivationOfAlgebraMap α hα halg) := sorry

/-- The identity filling has vanishing Ext⁰ class. -/
theorem extZeroOfAlgebraMap_id (L : FlatLift t f) :
    extZeroOfAlgebraMap (idAlgebraMap L) (idAlgebraMap_commutes L)
      (idAlgebraMap_isAlgebra L) = 0 := sorry

/-- Unique identity-cube algebra map whose derivation is the Hom(Ω, f^* 𝒞)
representative of an Ext⁰ class. -/
theorem existsUnique_perturbAlgebraMap (L : FlatLift t f) (ξ : extZeroNL t f) :
    ExistsUnique fun α :
        inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i ↦
      ∃ (hα : structureMap_commutes L.i L.i (𝟙 X) α)
        (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
          L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α),
          derivationOfAlgebraMap α hα halg = Hom.NaiveCotangent.extZeroToHom f ξ :=
  sorry

/-- The identity-cube perturbation of `(𝟙_{X'})^♯` by an Ext⁰ class, as the unique
`𝒪_{Y'}`-algebra map whose derivation is `Hom.NaiveCotangent.extZeroToHom f ξ`. -/
def perturbAlgebraMap (L : FlatLift t f) (ξ : extZeroNL t f) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  Classical.choose (existsUnique_perturbAlgebraMap L ξ)

/-- `perturbAlgebraMap L ξ` commutes with the structure-sheaf square. -/
theorem perturbAlgebraMap_commutes (L : FlatLift t f) (ξ : extZeroNL t f) :
    structureMap_commutes L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) := sorry

/-- `perturbAlgebraMap L ξ` is a morphism of `𝒪_{Y'}`-algebras. -/
theorem perturbAlgebraMap_isAlgebra (L : FlatLift t f) (ξ : extZeroNL t f) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f'))
      (perturbAlgebraMap L ξ) :=
  sorry

/-- `perturbAlgebraMap L ξ` commutes with the structure-sheaf square, is an
`𝒪_{Y'}`-algebra map, and has Ext⁰ class `ξ`. -/
theorem perturbAlgebraMap_spec (L : FlatLift t f) (ξ : extZeroNL t f) :
    structureMap_commutes L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) ∧
      isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
          L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f'))
          (perturbAlgebraMap L ξ) ∧
        extZeroOfAlgebraMap (perturbAlgebraMap L ξ)
            (perturbAlgebraMap_commutes L ξ)
            (perturbAlgebraMap_isAlgebra L ξ) = ξ :=
  sorry

/-- The zero Ext⁰ class perturbs the identity filling by the identity algebra map. -/
theorem perturbAlgebraMap_zero (L : FlatLift t f) :
    perturbAlgebraMap L 0 = idAlgebraMap L := sorry

/-- The unique morphism of thickenings over `Y'` lifting the identity-cube perturbation,
by the reconstruction theorem for morphisms of thickenings. -/
def ofExtZeroHom (L : FlatLift t f) (ξ : extZeroNL t f) : L.space ⟶ L.space :=
  Classical.choose
    (@existsUnique_hom_of_algebraMap _ _ _ _ _ _
      (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f' L.i L.i (𝟙 X)
      (@IsFirstOrderThickening.instIsThickening _ _ _ L.i (isFirstOrderThickening L))
      (@IsFirstOrderThickening.instIsThickening _ _ _ L.i (isFirstOrderThickening L))
      rfl rfl (Category.id_comp (L.i ≫ L.f')) (perturbAlgebraMap L ξ)
      (perturbAlgebraMap_spec L ξ).1 (perturbAlgebraMap_isAlgebra L ξ))

/-- `ofExtZeroHom L ξ` is over `Y'`. -/
theorem ofExtZeroHom_over (L : FlatLift t f) (ξ : extZeroNL t f) :
    ofExtZeroHom L ξ ≫ L.f' = L.f' := sorry

/-- `ofExtZeroHom L ξ` reduces to the identity on `X`. -/
theorem ofExtZeroHom_restrict (L : FlatLift t f) (ξ : extZeroNL t f) :
    L.i ≫ ofExtZeroHom L ξ = L.i := sorry

/-- `ofExtZeroHom L ξ` is an isomorphism. -/
theorem ofExtZeroHom_isIso (L : FlatLift t f) (ξ : extZeroNL t f) :
    IsIso (ofExtZeroHom L ξ) := sorry

/-- The Ext⁰-action on reducing-to-identity automorphisms, via identity-cube
perturbation and reconstruction of morphisms of thickenings. -/
def ofExtZero (L : FlatLift t f) (ξ : extZeroNL t f) : ReduceIdAuto L :=
  { hom := ofExtZeroHom L ξ
    over := ofExtZeroHom_over L ξ
    restrict := ofExtZeroHom_restrict L ξ
    isIso := ofExtZeroHom_isIso L ξ }

/-- `ofExtZero L ξ` is the geometric reconstruction of the identity-cube perturbation of `ξ`. -/
theorem ofExtZero_spec (L : FlatLift t f) (ξ : extZeroNL t f) :
    (ofExtZero L ξ).hom = ofExtZeroHom L ξ ∧
      IsHom L.f' L.f' L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) (ofExtZeroHom L ξ) ∧
        extZeroOfAlgebraMap (perturbAlgebraMap L ξ)
            (perturbAlgebraMap_commutes L ξ)
            (perturbAlgebraMap_isAlgebra L ξ) = ξ :=
  sorry

/-- The Ext⁰ class of a reducing-to-identity automorphism, as the Ext class of its
identity-cube algebra map. -/
def toExtZero {L : FlatLift t f} (φ : ReduceIdAuto L) : extZeroNL t f :=
  extZeroOfAlgebraMap (autoAlgebraMap φ) (autoAlgebraMap_commutes φ)
    (autoAlgebraMap_isAlgebra φ)

/-- `toExtZero φ` is the Ext⁰ class of the identity-cube algebra map of `φ`. -/
theorem toExtZero_spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    toExtZero φ = extZeroOfAlgebraMap (autoAlgebraMap φ)
        (autoAlgebraMap_commutes φ) (autoAlgebraMap_isAlgebra φ) ∧
      ofExtZero L (toExtZero φ) = φ := sorry

/-- The identity automorphism is the image of the zero Ext⁰ class. -/
theorem ofExtZero_zero (L : FlatLift t f) :
    ofExtZero L 0 = ReduceIdAuto.id L := sorry

/-- Automorphisms over the thickened base fixing the closed fibre correspond to Ext⁰ classes. -/
def reduceIdAutoEquiv (L : FlatLift t f) : ReduceIdAuto L ≃ extZeroNL t f where
  toFun φ := toExtZero φ
  invFun ξ := ofExtZero L ξ
  left_inv := sorry
  right_inv := sorry

/-- The forward chart sends a reducing-to-identity automorphism to its Ext⁰ class. -/
theorem reduceIdAutoEquiv_apply (L : FlatLift t f) (φ : ReduceIdAuto L) :
    reduceIdAutoEquiv L φ = toExtZero φ := sorry

/-- The inverse chart sends an Ext⁰ class to the identity-cube perturbation of
the identity automorphism. -/
theorem reduceIdAutoEquiv_symm_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    (reduceIdAutoEquiv L).symm ξ = ofExtZero L ξ := sorry

/-- The identity automorphism is sent to the zero Ext⁰ class. -/
theorem reduceIdAutoEquiv_zero (L : FlatLift t f) :
    reduceIdAutoEquiv L (ReduceIdAuto.id L) = 0 := sorry

end FlatLift
end AlgebraicGeometry.AlgebraicSpace.Thickening
