/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ComplexConic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Gluing
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic

/-!
# An explicit isomorphism `ℙ¹_ℂ ≅` the Fermat plane conic

This module constructs both legs of the isomorphism. The forward map is the degree-two
parametrization `[s : t] ↦ [s ^ 2 - t ^ 2 : -I * (s ^ 2 + t ^ 2) : 2 * s * t]`, glued from the
two standard affine charts of `ℙ¹_ℂ`. The inverse is glued from the two degree-one projections
`(X 0 + I * X 1, X 2)` and `(X 2, -X 0 + I * X 1)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.ComplexConic

/-- The degree-two parametrization of the Fermat conic by homogeneous coordinates on `ℙ¹_ℂ`. -/
def param : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  fun i ↦
    if i = 0 then MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2
    else if i = 1 then
      MvPolynomial.C (-Complex.I) * (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2)
    else 2 * MvPolynomial.X 0 * MvPolynomial.X 1

/-- Each coordinate of `param` is homogeneous of degree two. -/
theorem param_isHomogeneous (i : Fin 3) : (param i).IsHomogeneous 2 := sorry

/-- The parametrization lands on the Fermat equation. -/
theorem param_sq_sum : param 0 ^ 2 + param 1 ^ 2 + param 2 ^ 2 = 0 := sorry

/-- The polynomial map sending the plane coordinates to `param`. -/
def paramHom : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C param

/-- The Fermat equation lies in the kernel of `paramHom`. -/
theorem paramHom_equation : paramHom equation = 0 := sorry

/-- The Fermat ideal is contained in the kernel of `paramHom`. -/
theorem paramHom_eq_zero_of_mem_equationIdeal {f : MvPolynomial (Fin 3) ℂ}
    (hf : f ∈ equationIdeal.toIdeal) : paramHom f = 0 := sorry

/-- The induced map from the Fermat coordinate ring to the homogeneous coordinate ring of `ℙ¹_ℂ`. -/
def paramQuotientHom : coordinateRing →+* MvPolynomial (Fin 2) ℂ :=
  Ideal.Quotient.lift equationIdeal.toIdeal paramHom
    (fun _ hf ↦ paramHom_eq_zero_of_mem_equationIdeal hf)

/-- `paramQuotientHom` is the descent of `paramHom` through the Fermat quotient. -/
theorem paramQuotientHom_spec (f : MvPolynomial (Fin 3) ℂ) :
    paramQuotientHom (Ideal.Quotient.mk equationIdeal.toIdeal f) = paramHom f := sorry

/-- Dehomogenization of `paramQuotientHom` on a standard affine chart of `ℙ¹_ℂ`. -/
def dehomogParamQuotientHom (i : Fin 2) :
    coordinateRing →+* MvPolynomial (ULift.{0} (Fin 1)) ℂ :=
  (ProjectiveSpace.dehomogenizeAt 1 i Equiv.ulift.symm).comp paramQuotientHom

/-- The spectrum of the dehomogenized chart coordinate ring. -/
abbrev affineChartSpec : Scheme :=
  Spec (.of (MvPolynomial (ULift.{0} (Fin 1)) ℂ))

/-- Global sections of the affine chart spectrum, via the dehomogenized parametrization. -/
def affineChartSections (i : Fin 2) :
    coordinateRing →+* Γ(affineChartSpec, ⊤) :=
  (Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{0} (Fin 1)) ℂ))).inv.hom.comp
    (dehomogParamQuotientHom i)

/-- On each affine chart, the image of the Fermat irrelevant ideal is the unit ideal. -/
theorem affineChart_map_irrelevant_eq_top (i : Fin 2) :
    (HomogeneousIdeal.irrelevant grading).toIdeal.map (affineChartSections i) = ⊤ := sorry

/-- The parametrization on the spectrum of one dehomogenized affine chart. -/
def affineChartParametrization (i : Fin 2) : affineChartSpec ⟶ scheme :=
  Proj.fromOfGlobalSections grading (affineChartSections i)
    (affineChart_map_irrelevant_eq_top i)

/-- Comparison of a standard `ℙ¹` chart with the spectrum of its dehomogenized coordinate ring. -/
def chartToAffineSpec (i : Fin 2) :
    (ProjectiveLine.standardOpens ℂ i).toScheme ⟶ affineChartSpec :=
  (ProjectiveSpace.CoordinateChart.iso 1 i).hom ≫
    (AffineSpace.SpecIso (ULift.{0} (Fin 1)) (CommRingCat.of ℂ)).hom

/-- The parametrization restricted to one member of the standard two-chart cover of `ℙ¹_ℂ`. -/
def parametrizationChartMap (chart : (ProjectiveLine.standardCover ℂ).I₀) :
    (ProjectiveLine.standardCover ℂ).X chart ⟶ scheme :=
  chartToAffineSpec chart.down ≫ affineChartParametrization chart.down

/-- The two chart parametrizations agree on pairwise overlaps. -/
theorem parametrizationChartMap_compatible
    (i j : (ProjectiveLine.standardCover ℂ).I₀) :
    pullback.fst ((ProjectiveLine.standardCover ℂ).f i)
        ((ProjectiveLine.standardCover ℂ).f j) ≫
      parametrizationChartMap i =
    pullback.snd ((ProjectiveLine.standardCover ℂ).f i)
        ((ProjectiveLine.standardCover ℂ).f j) ≫
      parametrizationChartMap j := sorry

/-- The scheme morphism `ℙ¹_ℂ ⟶` Fermat conic obtained by gluing the chart parametrizations. -/
def parametrization : ProjectiveLine.scheme ℂ ⟶ scheme :=
  (ProjectiveLine.standardCover ℂ).glueMorphisms parametrizationChartMap
    parametrizationChartMap_compatible

/-- Linear forms used to project the Fermat conic onto `ℙ¹_ℂ` on a pair of complementary charts. -/
def projectionCoords (second : Bool) : Fin 2 → MvPolynomial (Fin 3) ℂ :=
  fun i ↦
    if second then
      if i = 0 then MvPolynomial.X 2
      else -MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1
    else if i = 0 then MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1
    else MvPolynomial.X 2

/-- The ungraded ring map sending the homogeneous coordinates of `ℙ¹_ℂ` to a projection chart. -/
def projectionRingHom (second : Bool) :
    MvPolynomial (Fin 2) ℂ →+* coordinateRing :=
  (Ideal.Quotient.mk equationIdeal.toIdeal).comp
    (MvPolynomial.eval₂Hom MvPolynomial.C (projectionCoords second))

/-- Each projection chart map preserves homogeneous degree. -/
theorem projectionRingHom_mem (second : Bool) {d : ℕ}
    {f : MvPolynomial (Fin 2) ℂ} (hf : f ∈ ProjectiveSpace.grading ℂ 1 d) :
    projectionRingHom second f ∈ grading d := sorry

/-- The graded ring map defining one projection chart. -/
def projectionGradedHom (second : Bool) :
    ProjectiveSpace.grading ℂ 1 →+*ᵍ grading where
  toRingHom := projectionRingHom second
  map_mem := projectionRingHom_mem second

/-- The natural open domain of one projection chart. -/
abbrev projectionChartOpen (chart : Bool) : scheme.Opens :=
  projMapDomain (projectionGradedHom chart)

/-- The universe-lifted pair of projection chart domains. -/
def projectionOpens : ULift.{0} Bool → scheme.Opens :=
  fun chart ↦ projectionChartOpen chart.down

/-- The two projection chart domains cover the Fermat conic. -/
theorem projectionOpens_isOpenCover :
    TopologicalSpace.IsOpenCover projectionOpens := sorry

/-- The two-chart open cover used to glue the inverse morphism. -/
def projectionCover : scheme.OpenCover :=
  scheme.openCoverOfIsOpenCover projectionOpens projectionOpens_isOpenCover

/-- The projective morphism defined by one projection chart formula. -/
def projectionChartMap (chart : projectionCover.I₀) :
    projectionCover.X chart ⟶ ProjectiveLine.scheme ℂ :=
  projMapMap (projectionGradedHom chart.down)

/-- The two projection chart formulas agree on their scheme-theoretic overlap. -/
theorem projectionChartMap_compatible (i j : projectionCover.I₀) :
    pullback.fst (projectionCover.f i) (projectionCover.f j) ≫ projectionChartMap i =
    pullback.snd (projectionCover.f i) (projectionCover.f j) ≫ projectionChartMap j := sorry

/-- The inverse morphism from the Fermat conic to `ℙ¹_ℂ`, glued from the two linear projections. -/
def projection : scheme ⟶ ProjectiveLine.scheme ℂ :=
  projectionCover.glueMorphisms projectionChartMap projectionChartMap_compatible

/-- The parametrization followed by the projection is the identity on `ℙ¹_ℂ`. -/
theorem parametrization_comp_projection :
    parametrization ≫ projection = 𝟙 (ProjectiveLine.scheme ℂ) := sorry

/-- The projection followed by the parametrization is the identity on the Fermat conic. -/
theorem projection_comp_parametrization :
    projection ≫ parametrization = 𝟙 scheme := sorry

/-- The explicit scheme isomorphism `ℙ¹_ℂ ≅` Fermat conic. -/
def projectiveLineIso : ProjectiveLine.scheme ℂ ≅ scheme where
  hom := parametrization
  inv := projection
  hom_inv_id := parametrization_comp_projection
  inv_hom_id := projection_comp_parametrization

/-- The forward arrow of `projectiveLineIso` is the glued parametrization. -/
theorem projectiveLineIso_hom : projectiveLineIso.hom = parametrization := rfl

/-- The inverse arrow of `projectiveLineIso` is the glued linear projection. -/
theorem projectiveLineIso_inv : projectiveLineIso.inv = projection := rfl

/-- The parametrization `ℙ¹_ℂ ⟶` Fermat conic is an isomorphism. -/
instance instIsIso_parametrization : IsIso parametrization :=
  projectiveLineIso.isIso_hom

/-- The parametrization commutes with the structure morphisms to `Spec ℂ`. -/
theorem parametrization_comp_toSpec :
    parametrization ≫ toSpec = ProjectiveLine.toSpec ℂ := sorry

/-- The projection commutes with the structure morphisms to `Spec ℂ`. -/
theorem projection_comp_toSpec :
    projection ≫ ProjectiveLine.toSpec ℂ = toSpec := sorry

end AlgebraicGeometry.ComplexConic
