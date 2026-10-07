module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.FiniteType
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap71.Lemma_71_11_11_Functor

/-!
# Étale-local finite type of relative Proj algebras

On affine objects of the small étale site, a graded `𝒪_X`-algebra is of finite type over its
degree-zero piece, or over `𝒪_X`, when a one-and-mul-preserving `Type u` section model has the
corresponding finite-type ring homomorphism. A morphism `π : P ⟶ X` is a relative `Proj` of `𝒜`
when each affine étale base change is the scheme `Proj` of such a section model.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Universe lift of a function on an affine étale chart to a section of the lifted structure
module. -/
def etaleBaseSection (U : affineEtaleSite X)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    (unitModule (smallEtaleTopology X) (commStructureSheafLift X)).val.obj (op U.obj) :=
  ULift.up.{u + 1, u} r

/-- `etaleBaseSection` is `ULift.up` of the unlifted function. -/
theorem etaleBaseSection_apply (U : affineEtaleSite X)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    etaleBaseSection U r = ULift.up.{u + 1, u} r :=
  sorry

/-- The canonical ring map from functions on an affine étale chart to the degree-zero piece of a
one-and-mul-preserving `Type u` section model, sending `r` to the model of `r • 𝒜.one`. -/
def etaleBaseToZero
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (commStructureSheaf X).obj.obj (op U.obj) →+* grading 0 where
  toFun r :=
    (model 0 (((gradedOneHom 𝒜).val.app (op U.obj)).hom (etaleBaseSection U r))).down
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `etaleBaseToZero` evaluates by transporting `gradedOneHom` along the degree-zero section
model. -/
theorem etaleBaseToZero_apply
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    etaleBaseToZero U model hModel r =
      (model 0 (((gradedOneHom 𝒜).val.app (op U.obj)).hom (etaleBaseSection U r))).down :=
  sorry

/-- The canonical ring map from functions on an affine étale chart to the ambient ring of a
one-and-mul-preserving `Type u` section model. -/
def etaleBaseToRing
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (commStructureSheaf X).obj.obj (op U.obj) →+* A :=
  (algebraMap (grading 0) A).comp (etaleBaseToZero U model hModel)

/-- `etaleBaseToRing` is the composite of `etaleBaseToZero` with the degree-zero inclusion. -/
theorem etaleBaseToRing_comp
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    (algebraMap (grading 0) A).comp (etaleBaseToZero U model hModel) =
      etaleBaseToRing U model hModel :=
  sorry

/-- `etaleBaseToRing` applies as the degree-zero inclusion after `etaleBaseToZero`. -/
theorem etaleBaseToRing_apply
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    (r : (commStructureSheaf X).obj.obj (op U.obj)) :
    etaleBaseToRing U model hModel r =
      algebraMap (grading 0) A (etaleBaseToZero U model hModel r) :=
  sorry

/-- The ambient ring of a nonnegative internal grading is of finite type over its degree-zero
piece. -/
def finiteTypeOverDegreeZero {A : Type u} [CommRing A]
    (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading] : Prop :=
  (algebraMap (grading 0) A).FiniteType

/-- `finiteTypeOverDegreeZero` is finite type of the canonical degree-zero inclusion. -/
theorem finiteTypeOverDegreeZero_iff {A : Type u} [CommRing A]
    (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading] :
    finiteTypeOverDegreeZero grading ↔ (algebraMap (grading 0) A).FiniteType :=
  sorry

/-- The canonical structure map of an affine étale section model is of finite type. -/
def finiteTypeOverEtaleBase
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) : Prop :=
  (etaleBaseToRing U model hModel).FiniteType

/-- `finiteTypeOverEtaleBase` is finite type of `etaleBaseToRing`. -/
theorem finiteTypeOverEtaleBase_iff
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    finiteTypeOverEtaleBase U model hModel ↔ (etaleBaseToRing U model hModel).FiniteType :=
  sorry

/-- A graded `𝒪_X`-algebra is of finite type as an `𝒜_0`-algebra when every affine étale chart
admits a one-and-mul-preserving `Type u` model whose ambient ring is of finite type over degree
zero. -/
def FiniteTypeAsDegreeZeroAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d)),
      @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model ∧
        @finiteTypeOverDegreeZero A hA grading hgraded

/-- Finite type as an `𝒜_0`-algebra is the affine-étale existence of a one-and-mul-preserving
`Type u` model of finite type over degree zero. -/
theorem finiteTypeAsDegreeZeroAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    FiniteTypeAsDegreeZeroAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d)),
          @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model ∧
            @finiteTypeOverDegreeZero A hA grading hgraded :=
  sorry

/-- A graded `𝒪_X`-algebra is of finite type as an `𝒪_X`-algebra when every affine étale chart
admits a one-and-mul-preserving `Type u` model whose canonical structure map is of finite type. -/
def FiniteTypeAsBaseAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
      @finiteTypeOverEtaleBase S X 𝒜 U A hA grading hgraded model hModel

/-- Finite type as an `𝒪_X`-algebra is the affine-étale existence of a one-and-mul-preserving
`Type u` model whose canonical structure map is of finite type. -/
theorem finiteTypeAsBaseAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    FiniteTypeAsBaseAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
          @finiteTypeOverEtaleBase S X 𝒜 U A hA grading hgraded model hModel :=
  sorry

/-- The canonical structure morphism of the scheme `Proj` of an affine étale section model,
obtained by composing `Proj.toSpecZero` with `Spec.map` of `etaleBaseToZero` and the affine
identification of the chart with the spectrum of its global sections. -/
def etaleChartProj
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    Proj grading ⟶ U.obj.left.left :=
  Proj.toSpecZero grading ≫
    Spec.map (CommRingCat.ofHom (etaleBaseToZero U model hModel)) ≫
    U.obj.left.left.isoSpec.inv

/-- `etaleChartProj` is `Proj.toSpecZero` followed by `Spec.map` of `etaleBaseToZero` and the
inverse of `Scheme.isoSpec` on the affine étale chart. -/
theorem etaleChartProj_comp
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    etaleChartProj U model hModel =
      Proj.toSpecZero grading ≫
        Spec.map (CommRingCat.ofHom (etaleBaseToZero U model hModel)) ≫
        U.obj.left.left.isoSpec.inv :=
  sorry

/-- The base change of `π` along an affine étale chart is the scheme `Proj` of the given
one-and-mul-preserving section model, as an algebraic space over that chart, via the canonical
structure morphism `etaleChartProj`. -/
def IsEtaleChartProj
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    {P : AlgebraicSpace S} (π : P ⟶ X) : Prop :=
  ∃ localIso : etaleBaseChangeSpace π U.obj ≅
      ofOver (Over.mk (etaleChartProj U model hModel ≫ U.obj.left.hom)),
    localIso.hom ≫ ofOverMap (Over.homMk (etaleChartProj U model hModel) rfl) =
      etaleBaseChangeSnd π U.obj

/-- `IsEtaleChartProj U model hModel π` means the base change of `π` along `U` is identified
with the scheme `Proj` of the model over `U` by an isomorphism whose triangle uses
`etaleChartProj`. -/
theorem isEtaleChartProj_iff
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model)
    {P : AlgebraicSpace S} (π : P ⟶ X) :
    IsEtaleChartProj U model hModel π ↔
      ∃ localIso : etaleBaseChangeSpace π U.obj ≅
          ofOver (Over.mk (etaleChartProj U model hModel ≫ U.obj.left.hom)),
        localIso.hom ≫ ofOverMap (Over.homMk (etaleChartProj U model hModel) rfl) =
          etaleBaseChangeSnd π U.obj :=
  sorry

/-- A morphism `π : P ⟶ X` is étale-locally the scheme `Proj` of a one-and-mul-preserving
`Type u` section model of `𝒜`, via the canonical structure morphism `etaleChartProj`. -/
def IsEtaleLocallyProj
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    {P : AlgebraicSpace S} (π : P ⟶ X) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
      @IsEtaleChartProj S X 𝒜 U A hA grading hgraded model hModel P π

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
            (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
          @IsEtaleChartProj S X 𝒜 U A hA grading hgraded model hModel P π :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
