/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Functor

/-!
# Affine-étale presentations of relative projective spectra

Canonical scalar maps and projective-spectrum structure morphisms specify relative Proj
presentations over affine étale charts, including compatibility with the base projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The canonical ring map from functions on an affine étale chart to the degree-zero piece of a
one-and-mul-preserving `Type u` section model, sending `r` to the model of `r • 𝒜.one`. -/
def etaleBaseToZero
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (commStructureSheaf X).obj.obj (op U.obj) →+* grading 0 := by
  let toZero : (commStructureSheaf X).obj.obj (op U.obj) → grading 0 :=
    fun r ↦
      (model 0 (((gradedOneHom 𝒜).val.app (op U.obj)).hom (ULift.up.{u + 1, u} r))).down
  have laws : toZero 1 = 1 ∧
      (∀ r s, toZero (r * s) = toZero r * toZero s) ∧
      toZero 0 = 0 ∧
      (∀ r s, toZero (r + s) = toZero r + toZero s) := sorry
  exact
    { toFun := toZero
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- The canonical degree-zero scalar map sends a function to the section model of its
scalar multiple of the sheaf unit. -/
theorem etaleBaseToZero_apply
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    etaleBaseToZero U model hModel r =
      (model 0 (((gradedOneHom 𝒜).val.app (op U.obj)).hom (ULift.up.{u + 1, u} r))).down :=
  rfl

/-- The canonical ring map from functions on an affine étale chart to the ambient ring of a
one-and-mul-preserving `Type u` section model. -/
def etaleBaseToRing
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (commStructureSheaf X).obj.obj (op U.obj) →+* A :=
  (algebraMap (grading 0) A).comp (etaleBaseToZero U model hModel)

/-- The scalar map to the ambient ring factors through the degree-zero inclusion. -/
theorem etaleBaseToRing_comp
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (algebraMap (grading 0) A).comp (etaleBaseToZero U model hModel) =
      etaleBaseToRing U model hModel :=
  rfl

/-- Evaluation of the scalar map to the ambient ring is the degree-zero inclusion of
the canonical degree-zero scalar map. -/
theorem etaleBaseToRing_apply
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    etaleBaseToRing U model hModel r =
      algebraMap (grading 0) A (etaleBaseToZero U model hModel r) :=
  rfl

/-- The canonical structure morphism of the scheme `Proj` of an affine étale section model,
obtained by composing `Proj.toSpecZero` with `Spec.map` of `etaleBaseToZero` and the affine
identification of the chart with the spectrum of its global sections. -/
def etaleChartProj
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    Proj grading ⟶ U.obj.left.left :=
  Proj.toSpecZero grading ≫
    Spec.map (CommRingCat.ofHom (etaleBaseToZero U model hModel)) ≫
    U.obj.left.left.isoSpec.inv

/-- The chart projective-spectrum morphism factors through the spectrum of the degree-zero
ring and the canonical spectrum identification of the affine chart. -/
theorem etaleChartProj_comp
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    etaleChartProj U model hModel =
      Proj.toSpecZero grading ≫
        Spec.map (CommRingCat.ofHom (etaleBaseToZero U model hModel)) ≫
        U.obj.left.left.isoSpec.inv :=
  rfl

/-- The base change of `π` along an affine étale chart is the scheme `Proj` of the given
one-and-mul-preserving section model, as an algebraic space over that chart, via the canonical
structure morphism `etaleChartProj`. -/
def IsEtaleChartProj
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    {P : AlgebraicSpace S} (π : P ⟶ X) : Prop :=
  ∃ localIso : etaleBaseChangeSpace π U.obj ≅
      ofOver (Over.mk (etaleChartProj U model hModel ≫ U.obj.left.hom)),
    localIso.hom ≫ ofOverMap (Over.homMk (etaleChartProj U model hModel) rfl) =
      etaleBaseChangeSnd π U.obj

/-- A chart has the projective-spectrum presentation precisely when its base change is
isomorphic to the model projective spectrum compatibly with the projection to the chart. -/
theorem isEtaleChartProj_iff
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    {P : AlgebraicSpace S} (π : P ⟶ X) :
    IsEtaleChartProj U model hModel π ↔
      ∃ localIso : etaleBaseChangeSpace π U.obj ≅
          ofOver (Over.mk (etaleChartProj U model hModel ≫ U.obj.left.hom)),
        localIso.hom ≫ ofOverMap (Over.homMk (etaleChartProj U model hModel) rfl) =
          etaleBaseChangeSnd π U.obj :=
  Iff.rfl

/-- A morphism `π : P ⟶ X` is étale-locally the scheme `Proj` of a one-and-mul-preserving
`Type u` section model of `𝒜`, via the canonical structure morphism `etaleChartProj`. -/
def IsEtaleLocallyProj
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    {P : AlgebraicSpace S} (π : P ⟶ X) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
      IsEtaleChartProj U model hModel π

/-- Étale-local scheme `Proj` is the affine-étale existence of a one-and-mul-preserving
`Type u` section model whose canonical projective-spectrum structure morphism realises the
base change of `π`. -/
theorem isEtaleLocallyProj_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    {P : AlgebraicSpace S} (π : P ⟶ X) :
    IsEtaleLocallyProj 𝒜 π ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
          IsEtaleChartProj U model hModel π :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
