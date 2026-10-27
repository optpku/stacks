/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity

/-!
# Naive cotangent comparison for represented algebraic spaces

The geometric étale-to-opens square induces a canonical comparison of naive cotangent
complexes. Its localization is an isomorphism in the derived category of module sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.Sheaf CategoryTheory.Sheaf.InternalCommRing
open Algebra Algebra.Extension Algebra.Generators Opposite MvPolynomial
open SheafOfModules.RingedSite CategoryTheory.Sheaf.FreeAlgebra ComplexShape
open scoped AlgebraicGeometry.AlgebraicSpace ZeroObject

noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
variable {S : Scheme.{u}}

/-- Degreewise étale inverse image of the opens-site naive cotangent complex. -/
def epsilonStarComplex {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    CochainComplex (ofOver X0).Modules ℤ :=
  ((SchemeRestriction.epsilonStar X0).mapHomologicalComplex (up ℤ)).obj
    (RingedSpace.naiveCotangent f0.left.toShHom)

/-- The conormal term of the degreewise inverse image is the inverse image of the conormal term. -/
theorem epsilonStarComplex_X_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X (-1) =
      (SchemeRestriction.epsilonStar X0).obj
        ((RingedSpace.naiveCotangent f0.left.toShHom).X (-1)) := rfl

/-- The differential term of the degreewise inverse image is the inverse image of that term. -/
theorem epsilonStarComplex_X_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X 0 =
      (SchemeRestriction.epsilonStar X0).obj
        ((RingedSpace.naiveCotangent f0.left.toShHom).X 0) := rfl

/-- An open subset determines its canonical étale chart. -/
private def ofOverHom_chart (X0 : Over S) (U : X0.left.Opensᵒᵖ) :
    (smallEtaleSite (ofOver X0))ᵒᵖ :=
  op ((SchemeRestriction.epsilon X0).base.obj U.unop)

/-- The structure coefficient sends a regular function to its restriction on the étale chart. -/
private def ofOverStructureCoeff {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    X0.left.sheaf.obj.obj U ⟶
      (commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U) :=
  CommRingCat.ofHom
    (((SchemeRestriction.opensCoefficientIso X0).hom.hom.app U) ≫
      (SchemeRestriction.epsilon X0).structureSheafMap.hom.app U).hom

/-- The direct-image coefficient map uses the inverse-image unit and the geometric square. -/
private def coefficientUnitApp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (V : Y0.left.Opensᵒᵖ) :
    Y0.left.sheaf.obj.obj V ⟶
      (commInverseImageStructureSheaf (ofOverMap f0)).obj.obj
        (ofOverHom_chart X0 (op ((TopologicalSpace.Opens.map f0.left.base).obj V.unop))) :=
  ofOverStructureCoeff (𝟙 Y0) V ≫
    (@CommRingCat.ofHom
      ((commStructureSheaf (ofOver Y0)).obj.obj (ofOverHom_chart Y0 V))
      (((commRingPushforward (ofOverMap f0)).obj
        (commInverseImageStructureSheaf (ofOverMap f0))).obj.obj (ofOverHom_chart Y0 V))
      (inferInstanceAs (CommRing ((commStructureSheaf (ofOver Y0)).obj.obj
        (ofOverHom_chart Y0 V))))
      (inferInstanceAs (CommRing (((commRingPushforward (ofOverMap f0)).obj
        (commInverseImageStructureSheaf (ofOverMap f0))).obj.obj (ofOverHom_chart Y0 V))))
      (((morphismOfTopoi (ofOverMap f0)).ringAdjunction.unit.app
        (structureSheaf (ofOver Y0))).hom.app (ofOverHom_chart Y0 V)).hom) ≫
    commRingPushforwardEvaluation (ofOverMap f0)
      (commInverseImageStructureSheaf (ofOverMap f0))
      (SchemeRestriction.smallPullbackSpaceIso f0
        ((SchemeRestriction.epsilon Y0).base.obj V.unop)).hom ≫
    (commInverseImageStructureSheaf (ofOverMap f0)).obj.map
      ((SchemeRestriction.restrictPullbackBaseIso f0).inv.app V.unop).op

/-- The coefficient maps induced by the geometric square commute with open restriction. -/
private theorem ofOverInverseImageCoefficient_naturality {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) {V W : Y0.left.Opensᵒᵖ} (i : V ⟶ W) :
    Y0.left.sheaf.obj.map i ≫ coefficientUnitApp f0 W =
      coefficientUnitApp f0 V ≫
        (commInverseImageStructureSheaf (ofOverMap f0)).obj.map
          ((SchemeRestriction.epsilon X0).base.map
            ((TopologicalSpace.Opens.map f0.left.base).map i.unop)).op := sorry

/-- The actual inverse-image coefficient comparison is the transpose of the geometric square. -/
private def ofOverInverseImageCoefficient {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf ⟶
      ((SchemeRestriction.epsilon X0).sheafPushforwardContinuous
        (A := CommRingCat.{u})).obj (commInverseImageStructureSheaf (ofOverMap f0)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f0.left.toShHom.hom.base).homEquiv _ _).symm
      ⟨{ app := coefficientUnitApp f0
         naturality := fun _ _ i ↦ ofOverInverseImageCoefficient_naturality f0 i }⟩

/-- The coefficient comparison respects the two structure-sheaf algebra maps. -/
private theorem ofOverInverseImageCoefficient_compatibility {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) (U : X0.left.Opensᵒᵖ) :
    (ofOverInverseImageCoefficient f0).hom.app U ≫
        (commInverseImageStructureSheafMap (ofOverMap f0)).hom.app (ofOverHom_chart X0 U) =
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.app U ≫
        ofOverStructureCoeff f0 U := by
  have square := SchemeRestriction.restrictPullbackBaseIso_structure f0
  sorry

/-- Section component of the inverse-image coefficient comparison. -/
private def ofOverInverseImageCoeffApp {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
      Y0.left.sheaf).obj.obj U ⟶
        (commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U) :=
  (ofOverInverseImageCoefficient f0).hom.app U

/-- The algebra structure on `𝒪_{X0}(U)` over `f0⁻¹𝒪_{Y0}(U)`. -/
@[reducible] private def schemeInverseImageAlgebra {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    Algebra (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      (X0.left.sheaf.obj.obj U) :=
  ((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.app U).hom.toAlgebra

/-- The canonical self-presentation of `𝒪_{X0}(U)` over `f0⁻¹𝒪_{Y0}(U)`. -/
private def schemePresentation {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  @Generators.self
    (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
    (X0.left.sheaf.obj.obj U)
    _ _ (schemeInverseImageAlgebra f0 U)

/-- Objectwise degree `-1` term of the scheme-level naive cotangent at an open subset. -/
private def schemeCotangentObj {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    ModuleCat.{u} (X0.left.sheaf.obj.obj U) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  ModuleCat.of _ (schemePresentation f0 U).toExtension.Cotangent

/-- Objectwise degree `0` term of the scheme-level naive cotangent at an open subset. -/
private def schemeCotangentSpaceObj {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    ModuleCat.{u} (X0.left.sheaf.obj.obj U) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  ModuleCat.of _ (schemePresentation f0 U).toExtension.CotangentSpace

/-- Polynomial-ring map of canonical presentations induced by the `ε`-square. -/
private def ofOverPresentationRingHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    MvPolynomial (X0.left.sheaf.obj.obj U)
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) →+*
      MvPolynomial ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))
        ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)) :=
  (MvPolynomial.map (ofOverInverseImageCoeffApp f0 U).hom).comp
    (MvPolynomial.rename fun s ↦ (ofOverStructureCoeff f0 U).hom s).toRingHom


/-- The polynomial coefficient map preserves the specified base algebra. -/
private theorem ofOverPresentationAlgHom_commutes {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  ∀ r : ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U,
    ofOverPresentationRingHom f0 U (MvPolynomial.C r) = algebraMap (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (MvPolynomial ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U))) r := sorry

/-- The polynomial comparison is an algebra homomorphism over the inverse-image coefficient ring. -/
private def ofOverPresentationAlgHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  ({ ofOverPresentationRingHom f0 U with
      commutes' := by exact ofOverPresentationAlgHom_commutes f0 U } :
    MvPolynomial (X0.left.sheaf.obj.obj U)
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) →ₐ[
      ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U]
      MvPolynomial ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))
        ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)))

/-- Kernel compatibility of the `ε`-square presentation map. -/
private theorem ofOverPresentationKer_le_comap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
    letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
    (schemePresentation f0 U).ker ≤
      (presentation (ofOverMap f0) (ofOverHom_chart X0 U)).ker.comap
        (ofOverPresentationRingHom f0 U) :=
  sorry

/-- Scalar tower of the coefficient map through `f_small⁻¹ 𝒪_Y`. -/
private theorem ofOver_isScalarTower_inverseImage {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
    letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
    letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
    -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
    letI : Algebra
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
        ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
            (ofOverHom_chart X0 U)).hom.comp
          (ofOverInverseImageCoeffApp f0 U).hom)
    IsScalarTower
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U))
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) := by
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- Scalar tower of `f0^♯` and `ε^♯` into `𝒪_X(ε(U))`. -/
private theorem ofOver_isScalarTower_structure {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
    letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
    -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
    letI : Algebra
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
        ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
            (ofOverHom_chart X0 U)).hom.comp
          (ofOverInverseImageCoeffApp f0 U).hom)
    IsScalarTower
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      (X0.left.sheaf.obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))  := by
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (ofOverInverseImageCoefficient_compatibility f0 U)) r


/-- The polynomial comparison respects coefficients and evaluation in the target ring. -/
private theorem ofOverPresentationHom_commutes {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `f⁻¹𝒪_Y`.
  letI := ofOver_isScalarTower_inverseImage f0 U
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_{X0}(U)`.
  letI := ofOver_isScalarTower_structure f0 U
  (∀ r : ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U, ofOverPresentationRingHom f0 U (algebraMap (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) ((schemePresentation f0 U).toExtension.Ring) r) =
    algebraMap ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)) ((presentation (ofOverMap f0) (ofOverHom_chart X0 U)).toExtension.Ring) (algebraMap (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) ((commInverseImageStructureSheaf (ofOverMap f0)).obj.obj (ofOverHom_chart X0 U)) r)) ∧
  (∀ x : (schemePresentation f0 U).toExtension.Ring, algebraMap ((presentation (ofOverMap f0) (ofOverHom_chart X0 U)).toExtension.Ring) ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) (ofOverPresentationRingHom f0 U x) =
    algebraMap (X0.left.sheaf.obj.obj U) ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U))
      (algebraMap ((schemePresentation f0 U).toExtension.Ring) (X0.left.sheaf.obj.obj U) x)) := sorry

/-- The geometric square induces a homomorphism of the two canonical algebra presentations. -/
private def ofOverPresentationHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `f⁻¹𝒪_Y`.
  letI := ofOver_isScalarTower_inverseImage f0 U
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_{X0}(U)`.
  letI := ofOver_isScalarTower_structure f0 U
  ({ toRingHom := ofOverPresentationRingHom f0 U
     toRingHom_algebraMap := by exact (ofOverPresentationHom_commutes f0 U).1
     algebraMap_toRingHom := by exact (ofOverPresentationHom_commutes f0 U).2 } :
    ((schemePresentation f0 U).toExtension).Hom
      ((presentation (ofOverMap f0) (ofOverHom_chart X0 U)).toExtension))

/-- Sheafification unit of the space-level conormal presheaf, evaluated at an `ε`-chart. -/
private def ofOverHom_negOne_sheafUnit {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    cotangentObj (ofOverMap f0) (ofOverHom_chart X0 U) ⟶
      ((SheafOfModules.forget _).obj
        (cotangentSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U) :=
  ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf (ofOver X0)).obj)).unit.app
    (cotangentPresheaf (ofOverMap f0))).app (ofOverHom_chart X0 U)

/-- Sheafification unit of the space-level cotangent-space presheaf, evaluated at an `ε`-chart. -/
private def ofOverHom_zero_sheafUnit {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    cotangentSpaceObj (ofOverMap f0) (ofOverHom_chart X0 U) ⟶
      ((SheafOfModules.forget _).obj
        (cotangentSpaceSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U) :=
  ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf (ofOver X0)).obj)).unit.app
    (cotangentSpacePresheaf (ofOverMap f0))).app (ofOverHom_chart X0 U)


/-- The specified comparison function is additive and linear over the structure ring. -/
private theorem ofOverHom_negOne_section_linear {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  let F : schemeCotangentObj f0 U → (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj (cotangentObj (ofOverMap f0) (ofOverHom_chart X0 U)) := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (presentation (ofOverMap f0) (ofOverHom_chart X0 U)).ker
            (ofOverPresentationAlgHom f0 U)
            (ofOverPresentationKer_le_comap f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x))
  (∀ x y, F (x + y) = F x + F y) ∧
    (∀ (r : X0.left.sheaf.obj.obj U) x, F (r • x) = r • F x) := sorry

/-- The coefficient comparison induces the conormal-module map on sections. -/
private def ofOverHom_negOne_section {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (cotangentObj (ofOverMap f0) (ofOverHom_chart X0 U)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (presentation (ofOverMap f0) (ofOverHom_chart X0 U)).ker
            (ofOverPresentationAlgHom f0 U)
            (ofOverPresentationKer_le_comap f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x))
      map_add' := by exact (ofOverHom_negOne_section_linear f0 U).1
      map_smul' := by exact (ofOverHom_negOne_section_linear f0 U).2 }

/-- Objectwise comparison of presentation cotangent-space terms of the `ε`-square. -/
private def ofOverHom_zero_section {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (cotangentSpaceObj (ofOverMap f0) (ofOverHom_chart X0 U)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at the chart.
  letI := inverseImageAlgebra (ofOverMap f0) (ofOverHom_chart X0 U)
  -- Local instance justification (noncanonical choice): objectwise coefficient of the `ε`-square.
  letI := (ofOverInverseImageCoeffApp f0 U).hom.toAlgebra
  -- Local instance justification (noncanonical choice): objectwise `ε^♯` algebra.
  letI := RingHom.toAlgebra (ofOverStructureCoeff f0 U).hom
  -- Local instance justification (noncanonical choice): composite algebra `f0⁻¹𝒪_{Y0}(U) → 𝒪_X(ε(U))`.
  letI : Algebra
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U)
      ((commStructureSheaf (ofOver X0)).obj.obj (ofOverHom_chart X0 U)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap (ofOverMap f0)).hom.app
          (ofOverHom_chart X0 U)).hom.comp
        (ofOverInverseImageCoeffApp f0 U).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `f⁻¹𝒪_Y`.
  letI := ofOver_isScalarTower_inverseImage f0 U
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_{X0}(U)`.
  letI := ofOver_isScalarTower_structure f0 U
  ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    (CotangentSpace.map (ofOverPresentationHom f0 U))

/-- Objectwise Zariski-side degree `-1` comparison. -/
private def ofOverHom_negOne_zariski_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (((SheafOfModules.forget _).obj
          (cotangentSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) :=
  ofOverHom_negOne_section f0 U ≫
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).map
      (ofOverHom_negOne_sheafUnit f0 U)

/-- Objectwise Zariski-side degree `0` comparison. -/
private def ofOverHom_zero_zariski_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶
      (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
        (((SheafOfModules.forget _).obj
          (cotangentSpaceSheaf (ofOverMap f0))).obj (ofOverHom_chart X0 U)) :=
  ofOverHom_zero_section f0 U ≫
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).map
      (ofOverHom_zero_sheafUnit f0 U)

/-- The sheaf polynomial presentation of `f0.left` on the opens site of `X0.left`. -/
private abbrev ofOverHom_schemePresentation {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :=
  CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
    ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
    (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)

/-- Coefficient ring of the sheaf polynomial presentation of `f0.left` on the open subset. -/
private abbrev ofOverHom_schemePullback {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
    Y0.left.sheaf).obj.obj U

/-- Underlying ring of the sheaf polynomial presentation of `f0.left` on the open subset. -/
private abbrev ofOverHom_schemeUnderlying {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  (CategoryTheory.Sheaf.FreeAlgebra.Presentation.underlying
    ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
    (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).obj.obj U

/-- Coefficient map from the opens-site inverse image of `𝒪_{Y0}` into the sheaf polynomial
presentation of `f0.left` on the open subset. -/
private def ofOverHom_negOne_affineCoeff {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    ofOverHom_schemePullback f0 U ⟶ ofOverHom_schemeUnderlying f0 U :=
  CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
      ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
      (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom) |>.hom.app U

/-- Polynomial evaluation sends each regular function to its generator in the sheaf
polynomial presentation and coefficients to their images under the presentation's base map. -/
private def ofOverHom_negOne_affinePolynomialMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    MvPolynomial (X0.left.sheaf.obj.obj U)
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) →+* ofOverHom_schemeUnderlying f0 U :=
  MvPolynomial.eval₂Hom
    (ofOverHom_negOne_affineCoeff f0 U).hom
    (fun s ↦
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).hom.app U s)


/-- The polynomial coefficient map preserves the specified base algebra. -/
private theorem ofOverHom_negOne_affinePolynomialAlgHom_commutes {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := (ofOverHom_negOne_affineCoeff f0 U).hom.toAlgebra
  ∀ r : ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U,
    ofOverHom_negOne_affinePolynomialMap f0 U (MvPolynomial.C r) = algebraMap (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (ofOverHom_schemeUnderlying f0 U) r := sorry

/-- The polynomial map to the sheaf presentation respects its coefficient algebra. -/
private def ofOverHom_negOne_affinePolynomialAlgHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := (ofOverHom_negOne_affineCoeff f0 U).hom.toAlgebra
  ({ ofOverHom_negOne_affinePolynomialMap f0 U with
      commutes' := by exact ofOverHom_negOne_affinePolynomialAlgHom_commutes f0 U } :
    MvPolynomial (X0.left.sheaf.obj.obj U)
        (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) →ₐ[
      ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U]
      ofOverHom_schemeUnderlying f0 U)

/-- Kernel compatibility of the affine polynomial map with the sheaf presentation. -/
private theorem ofOverHom_negOne_affinePolynomialMap_mem_ker {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
    letI := schemeInverseImageAlgebra f0 U
    (schemePresentation f0 U).ker ≤
      (conormalIdeal (ofOverHom_schemePresentation f0) U).comap
        (ofOverHom_negOne_affinePolynomialMap f0 U) :=
  sorry

/-- Degree `-1` term of the transported scheme naive cotangent at an open subset. -/
private abbrev ofOverHom_negOne_unpacked {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  ((RingedSpace.naiveCotangent f0.left.toShHom).X (-1)).val.obj U

/-- Degree `0` term of the transported scheme naive cotangent at an open subset. -/
private abbrev ofOverHom_zero_unpacked {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :=
  ((RingedSpace.naiveCotangent f0.left.toShHom).X 0).val.obj U


/-- The specified comparison function is additive and linear over the structure ring. -/
private theorem ofOverHom_negOne_affineHom_linear {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := (ofOverHom_negOne_affineCoeff f0 U).hom.toAlgebra
  let F : schemeCotangentObj f0 U → ofOverHom_negOne_unpacked f0 U := fun x ↦
        ((conormalSourcePresheafUnit (ofOverHom_schemePresentation f0)).app U
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (conormalIdeal (ofOverHom_schemePresentation f0) U)
            (ofOverHom_negOne_affinePolynomialAlgHom f0 U)
            (ofOverHom_negOne_affinePolynomialMap_mem_ker f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x)) :
          ofOverHom_negOne_unpacked f0 U)
  (∀ x y, F (x + y) = F x + F y) ∧
    (∀ (r : X0.left.sheaf.obj.obj U) x, F (r • x) = r • F x) := sorry

/-- The conormal-module comparison takes algebraic relations to their sheafified classes. -/
private def ofOverHom_negOne_affineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentObj f0 U ⟶ ofOverHom_negOne_unpacked f0 U :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): objectwise coefficient of the sheaf presentation.
  letI := (ofOverHom_negOne_affineCoeff f0 U).hom.toAlgebra
  ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    { toFun := fun x ↦
        ((conormalSourcePresheafUnit (ofOverHom_schemePresentation f0)).app U
          (Ideal.mapCotangent (schemePresentation f0 U).ker
            (conormalIdeal (ofOverHom_schemePresentation f0) U)
            (ofOverHom_negOne_affinePolynomialAlgHom f0 U)
            (ofOverHom_negOne_affinePolynomialMap_mem_ker f0 U)
            (Cotangent.val (P := (schemePresentation f0 U).toExtension) x)) :
          ofOverHom_negOne_unpacked f0 U)
      map_add' := by exact (ofOverHom_negOne_affineHom_linear f0 U).1
      map_smul' := by exact (ofOverHom_negOne_affineHom_linear f0 U).2 }

/-- A regular function determines the universal differential of its polynomial generator,
extended to the degree `0` term of the sheaf naive cotangent complex. -/
private def ofOverHom_zero_affineSection {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ)
    (a : X0.left.sheaf.obj.obj U) :
    ofOverHom_zero_unpacked f0 U :=
  ((extendRestrictAdj (ofOverHom_schemePresentation f0)).unit.app
      Ω(CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom))).val.app U
    (((relativeDifferential
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom))).app U).d
      ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
          ((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f0.left.toShHom)).hom.app U a))


/-- The specified comparison function is additive and linear over the structure ring. -/
private theorem ofOverHom_zero_affineHom_linear {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  let N := ofOverHom_zero_unpacked f0 U
  -- Local instance justification (defeq pin): pin N.isModule on the transported degree-zero module for the basis-map codomain.
  letI : Module (X0.left.sheaf.obj.obj U) N := N.isModule
  let φ :=
    (schemePresentation f0 U).cotangentSpaceBasis.constr
      (X0.left.sheaf.obj.obj U)
      (fun a ↦ (ofOverHom_zero_affineSection f0 U a : N))
  let F : schemeCotangentSpaceObj f0 U → ofOverHom_zero_unpacked f0 U := fun x ↦ φ x
  (∀ x y, F (x + y) = F x + F y) ∧
    (∀ (r : X0.left.sheaf.obj.obj U) x, F (r • x) = r • F x) := sorry

/-- The differential-module comparison sends a generator to its universal differential. -/
private def ofOverHom_zero_affineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    schemeCotangentSpaceObj f0 U ⟶ ofOverHom_zero_unpacked f0 U :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f0^♯`.
  letI := schemeInverseImageAlgebra f0 U
  let N := ofOverHom_zero_unpacked f0 U
  -- Local instance justification (defeq pin): pin N.isModule on the transported degree-zero module for the basis-map codomain.
  letI : Module (X0.left.sheaf.obj.obj U) N := N.isModule
  let φ :=
    (schemePresentation f0 U).cotangentSpaceBasis.constr
      (X0.left.sheaf.obj.obj U)
      (fun a ↦ (ofOverHom_zero_affineSection f0 U a : N))
  ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    { toFun := fun x ↦ φ x
      map_add' := by exact (ofOverHom_zero_affineHom_linear f0 U).1
      map_smul' := by exact (ofOverHom_zero_affineHom_linear f0 U).2 }

/-- Restriction of self-presentations sends each generator to its restricted generator. -/
private def schemeRestrictionHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V) :=
  -- Local instance justification (noncanonical choice): use the U component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): use the V component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 V
  -- Local instance justification (noncanonical choice): use inverse-image coefficient restriction along i as the algebra map.
  letI := (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
    Y0.left.sheaf).obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use structure-sheaf restriction along i as the algebra map.
  letI := (X0.left.sheaf.obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use coefficient restriction along i followed by the V structure map as the composite action.
  letI : Algebra (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj V) :=
    (((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.app V).hom.comp
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
        Y0.left.sheaf).obj.map i).hom).toAlgebra
  -- Local instance justification (proof-local temporary data): certify the displayed composite action through coefficient restriction and the V structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj V) (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  -- Local instance justification (proof-local temporary data): certify the structure-restriction tower using naturality of the scheme structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj U)
      (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦
      congrArg CommRingCat.Hom.hom
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.naturality i) |> fun h ↦ DFunLike.congr_fun h r)
  (Algebra.Generators.defaultHom (schemePresentation f0 U)
    (schemePresentation f0 V)).toExtensionHom

/-- Restriction on the objectwise presentation module is induced by polynomial restriction. -/
private def schemeCotangentMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V) :
    schemeCotangentObj f0 U ⟶
      (ModuleCat.restrictScalars (X0.left.sheaf.obj.map i).hom).obj (schemeCotangentObj f0 V) :=
  -- Local instance justification (noncanonical choice): use the U component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): use the V component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 V
  -- Local instance justification (noncanonical choice): use inverse-image coefficient restriction along i as the algebra map.
  letI := (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
    Y0.left.sheaf).obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use structure-sheaf restriction along i as the algebra map.
  letI := (X0.left.sheaf.obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use coefficient restriction along i followed by the V structure map as the composite action.
  letI : Algebra (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj V) :=
    (((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.app V).hom.comp
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
        Y0.left.sheaf).obj.map i).hom).toAlgebra
  -- Local instance justification (proof-local temporary data): certify the displayed composite action through coefficient restriction and the V structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj V) (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  -- Local instance justification (proof-local temporary data): certify the structure-restriction tower using naturality of the scheme structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj U)
      (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦
      congrArg CommRingCat.Hom.hom
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.naturality i) |> fun h ↦ DFunLike.congr_fun h r)
  ConcreteCategory.ofHom (C := ModuleCat (X0.left.sheaf.obj.obj U))
    (Cotangent.map (schemeRestrictionHom f0 i))

/-- Restriction on the objectwise presentation module is induced by polynomial restriction. -/
private def schemeCotangentSpaceMap {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V) :
    schemeCotangentSpaceObj f0 U ⟶
      (ModuleCat.restrictScalars (X0.left.sheaf.obj.map i).hom).obj (schemeCotangentSpaceObj f0 V) :=
  -- Local instance justification (noncanonical choice): use the U component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 U
  -- Local instance justification (noncanonical choice): use the V component of the scheme structure map as the coefficient action.
  letI := schemeInverseImageAlgebra f0 V
  -- Local instance justification (noncanonical choice): use inverse-image coefficient restriction along i as the algebra map.
  letI := (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
    Y0.left.sheaf).obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use structure-sheaf restriction along i as the algebra map.
  letI := (X0.left.sheaf.obj.map i).hom.toAlgebra
  -- Local instance justification (noncanonical choice): use coefficient restriction along i followed by the V structure map as the composite action.
  letI : Algebra (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj V) :=
    (((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.app V).hom.comp
      (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj
        Y0.left.sheaf).obj.map i).hom).toAlgebra
  -- Local instance justification (proof-local temporary data): certify the displayed composite action through coefficient restriction and the V structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj V) (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  -- Local instance justification (proof-local temporary data): certify the structure-restriction tower using naturality of the scheme structure map.
  letI : IsScalarTower (((TopCat.Sheaf.pullback CommRingCat.{u} f0.left.toShHom.hom.base).obj Y0.left.sheaf).obj.obj U) (X0.left.sheaf.obj.obj U)
      (X0.left.sheaf.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦
      congrArg CommRingCat.Hom.hom
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f0.left.toShHom).hom.naturality i) |> fun h ↦ DFunLike.congr_fun h r)
  ConcreteCategory.ofHom (C := ModuleCat (X0.left.sheaf.obj.obj U))
    (CotangentSpace.map (schemeRestrictionHom f0 i))

/-- Restriction on the conormal and differential modules preserves identities and composition. -/
private theorem schemeCotangentPresheaf_laws {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    ((∀ U, schemeCotangentMap f0 (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X0.left.ringCatSheaf.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (X0.left.ringCatSheaf.obj.map_id U))).inv.app
        (schemeCotangentObj f0 U)) ∧
    (∀ {U V W} (i : U ⟶ V) (j : V ⟶ W),
      schemeCotangentMap f0 (i ≫ j) = schemeCotangentMap f0 i ≫
        (ModuleCat.restrictScalars _).map (schemeCotangentMap f0 j) ≫
          (ModuleCat.restrictScalarsComp'
            (X0.left.ringCatSheaf.obj.map i).hom (X0.left.ringCatSheaf.obj.map j).hom
            (X0.left.ringCatSheaf.obj.map (i ≫ j)).hom
            (congrArg RingCat.Hom.hom (X0.left.ringCatSheaf.obj.map_comp i j))).inv.app
              (schemeCotangentObj f0 W))) ∧
    ((∀ U, schemeCotangentSpaceMap f0 (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X0.left.ringCatSheaf.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (X0.left.ringCatSheaf.obj.map_id U))).inv.app
        (schemeCotangentSpaceObj f0 U)) ∧
    (∀ {U V W} (i : U ⟶ V) (j : V ⟶ W),
      schemeCotangentSpaceMap f0 (i ≫ j) = schemeCotangentSpaceMap f0 i ≫
        (ModuleCat.restrictScalars _).map (schemeCotangentSpaceMap f0 j) ≫
          (ModuleCat.restrictScalarsComp'
            (X0.left.ringCatSheaf.obj.map i).hom (X0.left.ringCatSheaf.obj.map j).hom
            (X0.left.ringCatSheaf.obj.map (i ≫ j)).hom
            (congrArg RingCat.Hom.hom (X0.left.ringCatSheaf.obj.map_comp i j))).inv.app
              (schemeCotangentSpaceObj f0 W))) := sorry

/-- The presheaf of objectwise self-presentation modules with their polynomial restrictions. -/
private def schemeCotangentPresheaf {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    PresheafOfModules.{u} X0.left.ringCatSheaf.obj where
  obj := schemeCotangentObj f0
  map := schemeCotangentMap f0
  map_id := by exact (schemeCotangentPresheaf_laws f0).1.1
  map_comp := by exact (schemeCotangentPresheaf_laws f0).1.2

/-- The presheaf of objectwise self-presentation modules with their polynomial restrictions. -/
private def schemeCotangentSpacePresheaf {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    PresheafOfModules.{u} X0.left.ringCatSheaf.obj where
  obj := schemeCotangentSpaceObj f0
  map := schemeCotangentSpaceMap f0
  map_id := by exact (schemeCotangentPresheaf_laws f0).2.1
  map_comp := by exact (schemeCotangentPresheaf_laws f0).2.2

/-- The étale chart component is packed into the canonical ordinary restriction. -/
private def ofOverHom_negOne_targetHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
      ((cotangentSheaf (ofOverMap f0)).val.obj (ofOverHom_chart X0 U)) ⟶
        ((SchemeRestriction.ordinary X0).obj (cotangentSheaf (ofOverMap f0))).val.obj U :=
  (ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }) ≫
    ((SchemeRestriction.ordinaryIso X0).inv.app (cotangentSheaf (ofOverMap f0))).val.app U

/-- The étale chart component is packed into the canonical ordinary restriction. -/
private def ofOverHom_zero_targetHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    (U : X0.left.Opensᵒᵖ) :
    (ModuleCat.restrictScalars (ofOverStructureCoeff f0 U).hom).obj
      ((cotangentSpaceSheaf (ofOverMap f0)).val.obj (ofOverHom_chart X0 U)) ⟶
        ((SchemeRestriction.ordinary X0).obj (cotangentSpaceSheaf (ofOverMap f0))).val.obj U :=
  (ConcreteCategory.ofHom
    (C := ModuleCat (X0.left.sheaf.obj.obj U))
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }) ≫
    ((SchemeRestriction.ordinaryIso X0).inv.app (cotangentSpaceSheaf (ofOverMap f0))).val.app U

/-- The two presentation comparisons commute with restriction to open subsets. -/
private theorem schemeCotangentAffine_naturality {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (∀ {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V),
      (schemeCotangentPresheaf f0).map i ≫ (ModuleCat.restrictScalars _).map (ofOverHom_negOne_affineHom f0 V) =
        ofOverHom_negOne_affineHom f0 U ≫ ((RingedSpace.naiveCotangent f0.left.toShHom).X (-1)).val.map i) ∧
    (∀ {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V),
      (schemeCotangentSpacePresheaf f0).map i ≫ (ModuleCat.restrictScalars _).map (ofOverHom_zero_affineHom f0 V) =
        ofOverHom_zero_affineHom f0 U ≫ ((RingedSpace.naiveCotangent f0.left.toShHom).X 0).val.map i) := sorry

/-- The component maps form a morphism of module presheaves. -/
private def schemeCotangentAffinePresheafHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    schemeCotangentPresheaf f0 ⟶ ((RingedSpace.naiveCotangent f0.left.toShHom).X (-1)).val where
  app := ofOverHom_negOne_affineHom f0
  naturality := by exact (schemeCotangentAffine_naturality f0).1

/-- Transposition through sheafification gives the comparison of module sheaves. -/
private def ofOverHom_negOne_sheafAffineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.moduleSheafification X0.left.toRingedSpace).obj (schemeCotangentPresheaf f0) ⟶ ((RingedSpace.naiveCotangent f0.left.toShHom).X (-1)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X0.left.ringCatSheaf.obj)).homEquiv _ _).symm
    (schemeCotangentAffinePresheafHom f0)

/-- The component maps form a morphism of module presheaves. -/
private def schemeCotangentSpaceAffinePresheafHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    schemeCotangentSpacePresheaf f0 ⟶ ((RingedSpace.naiveCotangent f0.left.toShHom).X 0).val where
  app := ofOverHom_zero_affineHom f0
  naturality := by exact (schemeCotangentAffine_naturality f0).2

/-- Transposition through sheafification gives the comparison of module sheaves. -/
private def ofOverHom_zero_sheafAffineHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.moduleSheafification X0.left.toRingedSpace).obj (schemeCotangentSpacePresheaf f0) ⟶ ((RingedSpace.naiveCotangent f0.left.toShHom).X 0) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X0.left.ringCatSheaf.obj)).homEquiv _ _).symm
    (schemeCotangentSpaceAffinePresheafHom f0)

/-- The two presentation comparisons commute with restriction to open subsets. -/
private theorem schemeCotangentComparison_naturality {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (∀ {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V),
      (schemeCotangentPresheaf f0).map i ≫ (ModuleCat.restrictScalars _).map ((fun U ↦ ofOverHom_negOne_zariski_app f0 U ≫ ofOverHom_negOne_targetHom f0 U) V) =
        (fun U ↦ ofOverHom_negOne_zariski_app f0 U ≫ ofOverHom_negOne_targetHom f0 U) U ≫ ((SchemeRestriction.ordinary X0).obj (cotangentSheaf (ofOverMap f0))).val.map i) ∧
    (∀ {U V : X0.left.Opensᵒᵖ} (i : U ⟶ V),
      (schemeCotangentSpacePresheaf f0).map i ≫ (ModuleCat.restrictScalars _).map ((fun U ↦ ofOverHom_zero_zariski_app f0 U ≫ ofOverHom_zero_targetHom f0 U) V) =
        (fun U ↦ ofOverHom_zero_zariski_app f0 U ≫ ofOverHom_zero_targetHom f0 U) U ≫ ((SchemeRestriction.ordinary X0).obj (cotangentSpaceSheaf (ofOverMap f0))).val.map i) := sorry

/-- The component maps form a morphism of module presheaves. -/
private def schemeCotangentComparisonPresheafHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    schemeCotangentPresheaf f0 ⟶ ((SchemeRestriction.ordinary X0).obj (cotangentSheaf (ofOverMap f0))).val where
  app := fun U ↦ ofOverHom_negOne_zariski_app f0 U ≫ ofOverHom_negOne_targetHom f0 U
  naturality := by exact (schemeCotangentComparison_naturality f0).1

/-- Transposition through sheafification gives the comparison of module sheaves. -/
private def ofOverHom_negOne_sheafComparison {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.moduleSheafification X0.left.toRingedSpace).obj (schemeCotangentPresheaf f0) ⟶ ((SchemeRestriction.ordinary X0).obj (cotangentSheaf (ofOverMap f0))) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X0.left.ringCatSheaf.obj)).homEquiv _ _).symm
    (schemeCotangentComparisonPresheafHom f0)

/-- The component maps form a morphism of module presheaves. -/
private def schemeCotangentSpaceComparisonPresheafHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    schemeCotangentSpacePresheaf f0 ⟶ ((SchemeRestriction.ordinary X0).obj (cotangentSpaceSheaf (ofOverMap f0))).val where
  app := fun U ↦ ofOverHom_zero_zariski_app f0 U ≫ ofOverHom_zero_targetHom f0 U
  naturality := by exact (schemeCotangentComparison_naturality f0).2

/-- Transposition through sheafification gives the comparison of module sheaves. -/
private def ofOverHom_zero_sheafComparison {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.moduleSheafification X0.left.toRingedSpace).obj (schemeCotangentSpacePresheaf f0) ⟶ ((SchemeRestriction.ordinary X0).obj (cotangentSpaceSheaf (ofOverMap f0))) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X0.left.ringCatSheaf.obj)).homEquiv _ _).symm
    (schemeCotangentSpaceComparisonPresheafHom f0)

/-- The sheafified self-presentation comparison is invertible. -/
private theorem ofOverHom_negOne_sheafAffineHom_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (ofOverHom_negOne_sheafAffineHom f0) := sorry

/-- The opens-site comparison passes through the sheafified presentation. -/
@[no_expose] def ofOverHom_negOne_zariski {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.naiveCotangent f0.left.toShHom).X (-1) ⟶
      (SchemeRestriction.ordinary X0).obj (cotangentSheaf (ofOverMap f0)) :=
  (@asIso _ _ _ _ (ofOverHom_negOne_sheafAffineHom f0)
    (ofOverHom_negOne_sheafAffineHom_isIso f0)).inv ≫ ofOverHom_negOne_sheafComparison f0

/-- The étale comparison is the transpose of the opens-site comparison. -/
private def ofOverHom_negOne_etale {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X (-1) ⟶ (naiveCotangent (ofOverMap f0)).X (-1) :=
  ((SchemeRestriction.adjunction X0).homEquiv _ _).symm (ofOverHom_negOne_zariski f0)

/-- The degree (-1) component of the canonical comparison of naive cotangent complexes. -/
@[no_expose] def ofOverHom_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X (-1) ⟶ (naiveCotangent (ofOverMap f0)).X (-1) := by
  exact ofOverHom_negOne_etale f0

/-- The sheafified self-presentation comparison is invertible. -/
private theorem ofOverHom_zero_sheafAffineHom_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (ofOverHom_zero_sheafAffineHom f0) := sorry

/-- The opens-site comparison passes through the sheafified presentation. -/
@[no_expose] def ofOverHom_zero_zariski {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (RingedSpace.naiveCotangent f0.left.toShHom).X 0 ⟶
      (SchemeRestriction.ordinary X0).obj (cotangentSpaceSheaf (ofOverMap f0)) :=
  (@asIso _ _ _ _ (ofOverHom_zero_sheafAffineHom f0)
    (ofOverHom_zero_sheafAffineHom_isIso f0)).inv ≫ ofOverHom_zero_sheafComparison f0

/-- The étale comparison is the transpose of the opens-site comparison. -/
private def ofOverHom_zero_etale {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X 0 ⟶ (naiveCotangent (ofOverMap f0)).X 0 :=
  ((SchemeRestriction.adjunction X0).homEquiv _ _).symm (ofOverHom_zero_zariski f0)

/-- The degree 0 component of the canonical comparison of naive cotangent complexes. -/
@[no_expose] def ofOverHom_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (epsilonStarComplex f0).X 0 ⟶ (naiveCotangent (ofOverMap f0)).X 0 := by
  exact ofOverHom_zero_etale f0

/-- Degreewise components of the comparison `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}`. -/
private def ofOverHom_app {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) (n : ℤ) :
    (epsilonStarComplex f0).X n ⟶ (naiveCotangent (ofOverMap f0)).X n :=
  match n with
  | Int.negSucc 0 => ofOverHom_negOne f0
  | Int.ofNat 0 => ofOverHom_zero f0
  | _ => 0

/-- The degreewise comparison maps commute with differentials. -/
private theorem ofOverHom_app_comm {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ofOverHom_app f0 i ≫ (naiveCotangent (ofOverMap f0)).d i j =
      (epsilonStarComplex f0).d i j ≫ ofOverHom_app f0 j := sorry

/-- The canonical comparison `(ε* NL_{X0/Y0}) ⟶ NL_{X/Y}` of complexes of `𝒪_X`-modules. -/
@[no_expose] def ofOverHom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    epsilonStarComplex f0 ⟶ naiveCotangent (ofOverMap f0) where
  f n := by exact ofOverHom_app f0 n
  comm' i j hij := by exact ofOverHom_app_comm f0 i j hij

/-- The conormal component of the cochain comparison is its specified degree `-1` map. -/
theorem ofOverHom_f_negOne {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f (-1) = ofOverHom_negOne f0 := by exact rfl

/-- The differential component of the cochain comparison is its specified degree `0` map. -/
theorem ofOverHom_f_zero {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f 0 = ofOverHom_zero f0 := by exact rfl

/-- The nonzero components of the cochain comparison are the adjunction transposes of the opens-site comparison maps. -/
theorem ofOverHom_spec {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHom f0).f (-1) =
        ((SchemeRestriction.adjunction X0).homEquiv _ _).symm
          (ofOverHom_negOne_zariski f0) ∧
      (ofOverHom f0).f 0 =
        ((SchemeRestriction.adjunction X0).homEquiv _ _).symm
          (ofOverHom_zero_zariski f0) := ⟨rfl, rfl⟩

/-- The canonical morphism `ε* NL_{X0/Y0} ⟶ NL_{X/Y}` in `D(𝒪_X)`. -/
def ofOverHomDerived {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory.Q.obj (epsilonStarComplex f0) ⟶
      DerivedCategory.Q.obj (naiveCotangent (ofOverMap f0)) :=
  DerivedCategory.Q.map (ofOverHom f0)

/-- The comparison `ε* NL_{X0/Y0} ⟶ NL_{X/Y}` is an isomorphism in `D(𝒪_X)`. -/
instance ofOverHomDerived_isIso {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIso (ofOverHomDerived f0) :=
  sorry

/-- The canonical identification `ε* NL_{X0/Y0} ≅ NL_{X/Y}` in `D(𝒪_X)`. -/
def ofOverHomIso_derived {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    DerivedCategory.Q.obj (epsilonStarComplex f0) ≅
      DerivedCategory.Q.obj (naiveCotangent (ofOverMap f0)) :=
  asIso (ofOverHomDerived f0)

/-- The forward morphism of the derived identification is the localization of the canonical
cochain comparison from the inverse-image complex to the algebraic-space complex. -/
theorem ofOverHomIso_derived_hom {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    (ofOverHomIso_derived f0).hom = ofOverHomDerived f0 := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
