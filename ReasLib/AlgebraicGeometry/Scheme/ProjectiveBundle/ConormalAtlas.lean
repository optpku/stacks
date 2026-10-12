/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra.QuotientChart
public import ReasLib.AlgebraicGeometry.Scheme.Module.InvertibleQuotient.Trivialization
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.StandardOpen

/-!
# Conormal atlases for symmetric projective bundles

The local charts remember a trivialization of the quotient line and compatible
affine coordinates over an arbitrary refinement of the test scheme.  The
fraction, local conormal morphism, and global morphism are derived from these
coordinates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X}

/-- One genuine local quotient trivialization together with compatible split-quotient and
standard-open coordinates over an affine refinement of the test scheme. -/
structure ConormalChart (S : SymmetricPresentation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) where
  /-- The explicit sheaf-level trivialization of the quotient line. -/
  trivialization : CategoryTheory.InvertibleQuotient.OpenTrivialization
    (S.liftSourceQuotient f σ)
  /-- Symmetric homogeneous coordinates for the induced split quotient. -/
  quotientChart : AlgebraicGeometry.Proj.SymmetricQuotientChart
    (T.presheaf.obj (op trivialization.carrierOpen))
    (((Scheme.Modules.pullback f).obj ℰ).val.obj (op trivialization.carrierOpen))
  /-- The quotient in homogeneous coordinates is the sectionwise quotient followed by the
  chosen trivialization. -/
  quotientChart_spec : quotientChart.quotient = trivialization.quotient
  /-- The factorization through a compatible ambient standard open. -/
  standardOpen : StandardOpenFactorization S f σ trivialization.carrierOpen quotientChart

namespace ConormalChart

/-- Construct a local conormal chart from its quotient trivialization, split quotient coordinate,
and compatible standard-open factorization on the same affine refinement. -/
def ofCoordinates (S : SymmetricPresentation π ℰ) {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f)
    (trivialization : CategoryTheory.InvertibleQuotient.OpenTrivialization
      (S.liftSourceQuotient f σ))
    (quotientChart : AlgebraicGeometry.Proj.SymmetricQuotientChart
      (T.presheaf.obj (op trivialization.carrierOpen))
      (((Scheme.Modules.pullback f).obj ℰ).val.obj (op trivialization.carrierOpen)))
    (quotientChart_spec : quotientChart.quotient = trivialization.quotient)
    (standardOpen : StandardOpenFactorization S f σ
      trivialization.carrierOpen quotientChart) :
    ConormalChart S f σ :=
  { trivialization
    quotientChart
    quotientChart_spec
    standardOpen }

/-- The open subset underlying a local conormal chart. -/
abbrev carrierOpen {S : SymmetricPresentation π ℰ} {T : Scheme.{u}}
    {f : T ⟶ X} {σ : Lift π f} (C : ConormalChart S f σ) : T.Opens :=
  C.trivialization.carrierOpen

/-- A conormal chart consists of a compatible split quotient and affine refinement whose
restricted section is the symmetric-algebra augmentation. -/
theorem spec {S : SymmetricPresentation π ℰ} {T : Scheme.{u}}
    {f : T ⟶ X} {σ : Lift π f} (C : ConormalChart S f σ) :
    C.quotientChart.quotient = C.trivialization.quotient ∧
      C.standardOpen.augmentationMorphism ≫ C.standardOpen.targetCoordinate.hom =
        C.standardOpen.sourceCoordinate.hom ≫ C.standardOpen.restrictedSection ∧
      C.standardOpen.restrictedSection ≫ C.standardOpen.ambientOpen.ι =
        C.carrierOpen.ι ≫ σ.baseChangeSection := sorry

/-- The quotient-trivialization kernel is canonically transported to the kernel used by the
split quotient chart. -/
noncomputable def kernelComparison {S : SymmetricPresentation π ℰ}
    {T : Scheme.{u}} {f : T ⟶ X} {σ : Lift π f} (C : ConormalChart S f σ) :
    (CategoryTheory.InvertibleQuotient.conormalObject
      (S.liftSourceQuotient f σ)).val.obj (op C.carrierOpen) ⟶
      ModuleCat.of (T.presheaf.obj (op C.carrierOpen))
        (LinearMap.ker C.quotientChart.quotient) :=
  C.trivialization.conormalComparison.hom ≫
    eqToHom (congrArg
      (fun q : (((Scheme.Modules.pullback f).obj ℰ).val.obj (op C.carrierOpen)) →ₗ[
          T.presheaf.obj (op C.carrierOpen)] T.presheaf.obj (op C.carrierOpen) =>
        ModuleCat.of (T.presheaf.obj (op C.carrierOpen)) (LinearMap.ker q))
      C.quotientChart_spec.symm)

end ConormalChart

/-- The canonical indexing type of all local quotient trivializations with compatible
symmetric standard-open coordinates. -/
abbrev ConormalChartIndex (S : SymmetricPresentation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) := ConormalChart S f σ

/-- A conormal atlas asserts that the genuine local quotient charts form a basis.  Its chart
type itself is canonical, so no arbitrary family of maps is stored. -/
structure ConormalAtlas (S : SymmetricPresentation π ℰ) where
  /-- The chosen indexing type for local quotient charts. -/
  chartIndex : {T : Scheme.{u}} → (f : T ⟶ X) → Lift π f → Type u
  /-- Each index identifies a genuine local quotient chart. -/
  chartEquiv : ∀ {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f),
    chartIndex f σ ≃ ConormalChartIndex S f σ
  /-- Local quotient trivializations with homogeneous coordinates cover by a basis. -/
  basis_isBasis : ∀ {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f),
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun i : chartIndex f σ ↦ (chartEquiv f σ i).carrierOpen))

namespace ConormalAtlas

/-- The local quotient charts attached to a symmetric presentation form a basis. -/
theorem conormalCharts_isBasis (S : SymmetricPresentation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun i : ConormalChartIndex S f σ ↦ i.carrierOpen)) := sorry

/-- The canonical conormal atlas built from all actual quotient trivializations and compatible
standard-open coordinates on arbitrary affine refinements. -/
def ofPresentation (S : SymmetricPresentation π ℰ) : ConormalAtlas S where
  chartIndex := fun f σ ↦ ConormalChartIndex S f σ
  chartEquiv := fun _ _ ↦ Equiv.refl _
  basis_isBasis := conormalCharts_isBasis S

/-- The indices of the local quotient charts in a conormal atlas. -/
abbrev basisIndex {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) := A.chartIndex f σ

/-- The genuine local quotient chart represented by an atlas index. -/
def chartAt {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ) :
    ConormalChartIndex S f σ := A.chartEquiv f σ i

/-- The open subset underlying a local conormal chart. -/
def basisOpen {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ) :
    T.Opens := (A.chartAt f σ i).carrierOpen

/-- The homogeneous fraction `k / s` in the standard-open coordinate ring of a chart. -/
noncomputable def fraction {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ)
    (k : LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) :
    (A.chartAt f σ i).quotientChart.away :=
  (A.chartAt f σ i).quotientChart.symmetricQuotientFraction k

/-- The numerator ideal element whose cotangent class represents `k / s` on a chart. -/
def fractionIdeal {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ)
    (k : LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) :
    SymmetricAlgebra.augmentationIdeal
      (T.presheaf.obj (op (A.chartAt f σ i).carrierOpen))
      (LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) :=
  (A.chartAt f σ i).quotientChart.symmetricQuotientConormalNumerator k

/-- The canonical map from a chart kernel to the augmentation cotangent module. -/
def fractionKernelMap {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ) :
    ModuleCat.of (T.presheaf.obj (op (A.chartAt f σ i).carrierOpen))
        (LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) ⟶
      ModuleCat.of (T.presheaf.obj (op (A.chartAt f σ i).carrierOpen))
        (SymmetricAlgebra.augmentationIdeal
          (T.presheaf.obj (op (A.chartAt f σ i).carrierOpen))
          (LinearMap.ker (A.chartAt f σ i).quotientChart.quotient)).Cotangent :=
  ModuleCat.ofHom
    (AlgebraicGeometry.Proj.symmetricQuotientKernelToConormal
      (A.chartAt f σ i).quotientChart)

/-- The basis-local conormal morphism obtained from quotient-line trivialization and the
symmetric-algebra augmentation calculation. -/
noncomputable def localLinearMap {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    (i : A.basisIndex f σ) :
    (CategoryTheory.InvertibleQuotient.conormalObject
      (S.liftSourceQuotient f σ)).val.obj
        (op (A.chartAt f σ i).carrierOpen) ⟶
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj
        (op (A.chartAt f σ i).carrierOpen) :=
  ConormalChart.kernelComparison (A.chartAt f σ i) ≫ A.fractionKernelMap f σ i ≫
    (A.chartAt f σ i).standardOpen.conormalTransport

/-- The local conormal class is the image of a kernel numerator under the canonical
augmentation-cotangent map and the affine chart identification. -/
noncomputable def fractionClass {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    (i : A.basisIndex f σ)
    (k : LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) :
    (Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj
      (op (A.chartAt f σ i).carrierOpen) :=
  (A.chartAt f σ i).standardOpen.conormalTransport
    ((A.chartAt f σ i).quotientChart.symmetricQuotientFractionClass k)

/-- Changing the lift of a quotient generator does not change its conormal class. -/
theorem fractionClass_changeGenerator {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    (i : A.basisIndex f σ)
    (s' : ((Scheme.Modules.pullback f).obj ℰ).val.obj
      (op (A.chartAt f σ i).carrierOpen))
    (hs' : (A.chartAt f σ i).quotientChart.quotient s' = 1)
    (k : LinearMap.ker (A.chartAt f σ i).quotientChart.quotient) :
    A.fractionClass f σ i k =
      (A.chartAt f σ i).standardOpen.conormalTransport
        (({ (A.chartAt f σ i).quotientChart with
            generatorLift := s', generatorLift_spec := hs' } :
          AlgebraicGeometry.Proj.SymmetricQuotientChart
            (T.presheaf.obj (op (A.chartAt f σ i).carrierOpen))
            (((Scheme.Modules.pullback f).obj ℰ).val.obj
              (op (A.chartAt f σ i).carrierOpen))).symmetricQuotientFractionClass k) := sorry

/-- The basis-local conormal maps commute with restriction between local quotient charts. -/
theorem localLinearMap_naturality {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    {i j : (InducedCategory T.Opens (A.basisOpen f σ))ᵒᵖ} (r : i ⟶ j) :
    (((inducedFunctor (A.basisOpen f σ)).op ⋙
        (CategoryTheory.InvertibleQuotient.conormalObject
          (S.liftSourceQuotient f σ)).presheaf).map r) ≫
        (forget₂ _ _).map (A.localLinearMap f σ j.unop) =
      (forget₂ _ _).map (A.localLinearMap f σ i.unop) ≫
        (((inducedFunctor (A.basisOpen f σ)).op ⋙
          (Scheme.Hom.conormalSheaf σ.baseChangeSection).presheaf).map r) := sorry

/-- The additive-presheaf morphism assembled from the local homogeneous-fraction maps. -/
noncomputable def localMap {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (inducedFunctor (A.basisOpen f σ)).op ⋙
        (CategoryTheory.InvertibleQuotient.conormalObject
          (S.liftSourceQuotient f σ)).presheaf ⟶
      (inducedFunctor (A.basisOpen f σ)).op ⋙
        (Scheme.Hom.conormalSheaf σ.baseChangeSection).presheaf where
  app i := (forget₂ _ _).map (A.localLinearMap f σ i.unop)
  naturality _ _ r := A.localLinearMap_naturality f σ r

/-- The underlying additive-presheaf map obtained by extending the local conormal maps from
the basis. -/
noncomputable def extendedMapPresheaf {S : SymmetricPresentation π ℰ}
    (A : ConormalAtlas S) {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    (CategoryTheory.InvertibleQuotient.conormalObject
      (S.liftSourceQuotient f σ)).presheaf ⟶
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom
    (CategoryTheory.InvertibleQuotient.conormalObject
      (S.liftSourceQuotient f σ)).presheaf
    ⟨(Scheme.Hom.conormalSheaf σ.baseChangeSection).presheaf,
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).isSheaf⟩
    (A.basis_isBasis f σ) (A.localMap f σ)

/-- The basis extension of the local conormal maps is linear over the structure sheaf. -/
theorem map_smul {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    (U : T.Opensᵒᵖ) (r : T.presheaf.obj U)
    (m : (CategoryTheory.InvertibleQuotient.conormalObject
      (S.liftSourceQuotient f σ)).val.obj U) :
    (A.extendedMapPresheaf f σ).app U (r • m) =
      (((Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj U).smul r).hom
        ((A.extendedMapPresheaf f σ).app U m) := sorry

/-- The global conormal morphism obtained by basis extension of the local `k / s` maps. -/
noncomputable def map {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    CategoryTheory.InvertibleQuotient.conormalObject (S.liftSourceQuotient f σ) ⟶
      Scheme.Hom.conormalSheaf σ.baseChangeSection :=
  (Scheme.Modules.fullyFaithfulToPresheafOfModules).preimage
    (PresheafOfModules.homMk (A.extendedMapPresheaf f σ) (A.map_smul f σ))

/-- The global conormal morphism restricts to the canonical local map on each chart. -/
theorem map_restrict {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ) :
    (A.map f σ).app (A.basisOpen f σ i) =
      (forget₂ _ _).map (A.localLinearMap f σ i) := sorry

/-- Each basis-local homogeneous-fraction conormal morphism is an isomorphism. -/
theorem localMap_isIso {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (i : A.basisIndex f σ) :
    IsIso (A.localLinearMap f σ i) := sorry

/-- The global conormal morphism obtained from the conormal atlas is an isomorphism. -/
theorem map_isIso {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    IsIso (A.map f σ) := sorry

/-- A conormal atlas exposes a basis of genuine split quotient charts and the canonical local
kernel-to-conormal calculation on every chart. -/
theorem spec {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    TopologicalSpace.Opens.IsBasis
        (Set.range (fun i : A.basisIndex f σ ↦ A.basisOpen f σ i)) ∧
      ∀ i : A.basisIndex f σ,
        Function.Bijective
          (AlgebraicGeometry.Proj.symmetricQuotientKernelToConormal
            (A.chartAt f σ i).quotientChart) := sorry

/-- A module morphism agreeing with the local fraction maps on the atlas basis is the global
atlas map. -/
theorem map_unique {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f)
    (φ : CategoryTheory.InvertibleQuotient.conormalObject
        (S.liftSourceQuotient f σ) ⟶ Scheme.Hom.conormalSheaf σ.baseChangeSection)
    (hφ : ∀ i : A.basisIndex f σ,
      φ.app (A.basisOpen f σ i) =
        (forget₂ _ _).map (A.localLinearMap f σ i)) :
    φ = A.map f σ := sorry

/-- Equality on the pulled-back basis implies compatibility of the global conormal maps with
precomposition. -/
theorem map_precomp {S : SymmetricPresentation π ℰ} (A : ConormalAtlas S)
    {T R : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (sourceComparison :
      (Scheme.Modules.pullback g).obj
          (CategoryTheory.InvertibleQuotient.conormalObject
            (S.liftSourceQuotient f σ)) ⟶
        CategoryTheory.InvertibleQuotient.conormalObject
          (S.liftSourceQuotient (g ≫ f) (σ.precomp g)))
    (targetComparison :
      (Scheme.Modules.pullback g).obj
          (Scheme.Hom.conormalSheaf σ.baseChangeSection) ⟶
        Scheme.Hom.conormalSheaf (σ.precomp g).baseChangeSection)
    (h_basis : ∀ i : A.basisIndex (g ≫ f) (σ.precomp g),
      (((Scheme.Modules.pullback g).map (A.map f σ) ≫ targetComparison).app
          (A.basisOpen (g ≫ f) (σ.precomp g) i)) =
        ((sourceComparison ≫ A.map (g ≫ f) (σ.precomp g)).app
          (A.basisOpen (g ≫ f) (σ.precomp g) i))) :
    (Scheme.Modules.pullback g).map (A.map f σ) ≫ targetComparison =
      sourceComparison ≫ A.map (g ≫ f) (σ.precomp g) := sorry

end ConormalAtlas

end AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation
