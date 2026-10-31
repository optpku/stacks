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
theorem param_isHomogeneous (i : Fin 3) : (param i).IsHomogeneous 2 := by
  fin_cases i
  · simpa [param] using
      ((MvPolynomial.isHomogeneous_X_pow (R := ℂ) (0 : Fin 2) 2).sub
        (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (1 : Fin 2) 2))
  · simpa [param] using
      ((MvPolynomial.isHomogeneous_X_pow (R := ℂ) (0 : Fin 2) 2).add
        (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (1 : Fin 2) 2)).C_mul
          (-Complex.I)
  · have h2 : (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 := map_ofNat _ 2
    simpa [param, h2, mul_assoc] using
      ((MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 2)).mul
        (MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2))).C_mul (2 : ℂ)

/-- The parametrization lands on the Fermat equation. -/
theorem param_sq_sum : param 0 ^ 2 + param 1 ^ 2 + param 2 ^ 2 = 0 := by
  have hI : (MvPolynomial.C (-Complex.I) : MvPolynomial (Fin 2) ℂ) ^ 2 = -1 := by
    rw [← map_pow, neg_sq, Complex.I_sq, map_neg, map_one]
  change (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2) ^ 2 +
    (MvPolynomial.C (-Complex.I) * (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2)) ^ 2 +
    (2 * MvPolynomial.X 0 * MvPolynomial.X 1) ^ 2 = 0
  rw [mul_pow, hI]
  ring

/-- The polynomial map sending the plane coordinates to `param`. -/
def paramHom : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C param

/-- The Fermat equation lies in the kernel of `paramHom`. -/
theorem paramHom_equation : paramHom equation = 0 := by
  simp only [paramHom, equation, map_add, map_pow, MvPolynomial.eval₂Hom_X']
  exact param_sq_sum

/-- The Fermat ideal is contained in the kernel of `paramHom`. -/
theorem paramHom_eq_zero_of_mem_equationIdeal {f : MvPolynomial (Fin 3) ℂ}
    (hf : f ∈ equationIdeal.toIdeal) : paramHom f = 0 := by
  apply RingHom.mem_ker.mp
  apply (show equationIdeal.toIdeal ≤ RingHom.ker paramHom from ?_) hf
  rw [equationIdeal_toIdeal]
  rw [Ideal.span_singleton_le_iff_mem]
  exact RingHom.mem_ker.mpr paramHom_equation

/-- The induced map from the Fermat coordinate ring to the homogeneous coordinate ring of `ℙ¹_ℂ`. -/
def paramQuotientHom : coordinateRing →+* MvPolynomial (Fin 2) ℂ :=
  Ideal.Quotient.lift equationIdeal.toIdeal paramHom
    (fun _ hf ↦ paramHom_eq_zero_of_mem_equationIdeal hf)

/-- `paramQuotientHom` is the descent of `paramHom` through the Fermat quotient. -/
theorem paramQuotientHom_spec (f : MvPolynomial (Fin 3) ℂ) :
    paramQuotientHom (Ideal.Quotient.mk equationIdeal.toIdeal f) = paramHom f := by
  rfl

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
    (HomogeneousIdeal.irrelevant grading).toIdeal.map (affineChartSections i) = ⊤ := by
  have hunit : IsUnit (2 : MvPolynomial (ULift.{0} (Fin 1)) ℂ) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℂ) ≠ 0)).map
        (MvPolynomial.C : ℂ →+* MvPolynomial (ULift.{0} (Fin 1)) ℂ)
  have htop (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 1)
      (heval : dehomogParamQuotientHom i (Ideal.Quotient.mk equationIdeal.toIdeal p) = 2) :
      (HomogeneousIdeal.irrelevant grading).toIdeal.map (affineChartSections i) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem _
        (HomogeneousIdeal.mem_irrelevant_of_mem grading Nat.zero_lt_one
          (GradedAlgebra.Quotient.mk_mem_grading (ProjectiveSpace.grading ℂ 2)
            equationIdeal.toIdeal hp)))
    change IsUnit ((Scheme.ΓSpecIso
      (.of (MvPolynomial (ULift.{0} (Fin 1)) ℂ))).inv.hom
        (dehomogParamQuotientHom i (Ideal.Quotient.mk equationIdeal.toIdeal p)))
    rw [heval]
    exact hunit.map _
  have hI : (MvPolynomial.C Complex.I : MvPolynomial (Fin 2) ℂ) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  fin_cases i
  · apply htop (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1)
    · exact (MvPolynomial.isHomogeneous_X _ _).add
        (MvPolynomial.isHomogeneous_C_mul_X _ _)
    · have hp : paramHom (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1) =
          2 * MvPolynomial.X 0 ^ 2 := by
        simp [paramHom, param]
        ring_nf
        rw [hI]
        ring
      change (ProjectiveSpace.dehomogenizeAt (R := ℂ) 1 0 Equiv.ulift.symm)
        (paramHom (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1)) = 2
      rw [hp]
      simp only [map_mul, map_pow, map_ofNat]
      simp [ProjectiveSpace.dehomogenizeAt]
  · apply htop (-MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1)
    · exact (MvPolynomial.isHomogeneous_X _ _).neg.add
        (MvPolynomial.isHomogeneous_C_mul_X _ _)
    · have hp : paramHom (-MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1) =
          2 * MvPolynomial.X 1 ^ 2 := by
        simp [paramHom, param]
        ring_nf
        rw [hI]
        ring
      change (ProjectiveSpace.dehomogenizeAt (R := ℂ) 1 1 Equiv.ulift.symm)
        (paramHom (-MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1)) = 2
      rw [hp]
      simp only [map_mul, map_pow, map_ofNat]
      simp [ProjectiveSpace.dehomogenizeAt]

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
    projectionRingHom second f ∈ grading d := by
  apply GradedAlgebra.Quotient.mk_mem_grading (ProjectiveSpace.grading ℂ 2)
    equationIdeal.toIdeal
  change (MvPolynomial.eval₂Hom MvPolynomial.C (projectionCoords second) f).IsHomogeneous d
  have hcoords : ∀ i, (projectionCoords second i).IsHomogeneous 1 := by
    intro i
    by_cases h : second
    · fin_cases i
      · simpa [projectionCoords, h] using
          (MvPolynomial.isHomogeneous_X (R := ℂ) (2 : Fin 3))
      · simpa [projectionCoords, h] using
          ((MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 3)).neg.add
            (MvPolynomial.isHomogeneous_C_mul_X (R := ℂ) Complex.I (1 : Fin 3)))
    · fin_cases i
      · simpa [projectionCoords, h] using
          ((MvPolynomial.isHomogeneous_X (R := ℂ) (0 : Fin 3)).add
            (MvPolynomial.isHomogeneous_C_mul_X (R := ℂ) Complex.I (1 : Fin 3)))
      · simpa [projectionCoords, h] using
          (MvPolynomial.isHomogeneous_X (R := ℂ) (2 : Fin 3))
  simpa only [MvPolynomial.coe_eval₂Hom, one_mul] using
    (MvPolynomial.IsHomogeneous.eval₂ hf MvPolynomial.C (projectionCoords second)
      (fun r ↦ MvPolynomial.isHomogeneous_C _ _) hcoords)

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
    TopologicalSpace.IsOpenCover projectionOpens := by
  let q := Ideal.Quotient.mk equationIdeal.toIdeal
  have hcover : (⨆ j : Fin 3, Proj.basicOpen grading (q (MvPolynomial.X j))) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · intro j
      exact ⟨1, GradedAlgebra.Quotient.mk_mem_grading (ProjectiveSpace.grading ℂ 2)
        equationIdeal.toIdeal (MvPolynomial.isHomogeneous_X _ _)⟩
    · apply top_unique
      intro p hp
      clear hp
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective p
      induction f using MvPolynomial.induction_on with
      | C r =>
        exact (Algebra.adjoin (grading 0)
          (Set.range (fun j : Fin 3 ↦ q (MvPolynomial.X j)))).algebraMap_mem
            ⟨q (MvPolynomial.C r),
            GradedAlgebra.Quotient.mk_mem_grading (ProjectiveSpace.grading ℂ 2)
              equationIdeal.toIdeal (MvPolynomial.isHomogeneous_C _ _)⟩
      | add f g hf hg => simpa only [map_add] using add_mem hf hg
      | mul_X f j hf =>
        simpa only [map_mul] using mul_mem hf
          (Algebra.subset_adjoin ⟨j, rfl⟩)
  change (⨆ chart, projectionOpens chart) = ⊤
  apply top_le_iff.mp
  rw [← hcover]
  refine iSup_le fun j x hx ↦ ?_
  by_contra hn
  have hvan (second : Bool) (k : Fin 2) :
      projectionRingHom second (MvPolynomial.X k) ∈ x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    apply hn
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨ULift.up second, ?_⟩
    exact (basicOpen_le_projMapDomain (projectionGradedHom second) Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X ℂ k)) h
  let P := x.asHomogeneousIdeal.toIdeal
  have hleft : q (MvPolynomial.X 0) + q (MvPolynomial.C Complex.I) * q (MvPolynomial.X 1)
      ∈ P := by
    simpa [projectionRingHom, projectionCoords, q, P] using hvan false 0
  have hright : -q (MvPolynomial.X 0) + q (MvPolynomial.C Complex.I) * q (MvPolynomial.X 1)
      ∈ P := by
    simpa [projectionRingHom, projectionCoords, q, P] using hvan true 1
  have htwo : IsUnit (2 : coordinateRing) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℂ) ≠ 0)).map (q.comp MvPolynomial.C)
  have hI : IsUnit (q (MvPolynomial.C Complex.I)) :=
    ((isUnit_iff_ne_zero.mpr Complex.I_ne_zero).map MvPolynomial.C).map q
  have hzero : q (MvPolynomial.X 0) ∈ P := by
    apply (P.unit_mul_mem_iff_mem htwo).mp
    convert P.sub_mem hleft hright using 1
    ring
  have hone : q (MvPolynomial.X 1) ∈ P := by
    apply (P.unit_mul_mem_iff_mem (htwo.mul hI)).mp
    convert P.add_mem hleft hright using 1
    ring
  have htwo' : q (MvPolynomial.X 2) ∈ P := by
    simpa [projectionRingHom, projectionCoords, q, P] using hvan true 0
  fin_cases j
  · exact hx hzero
  · exact hx hone
  · exact hx htwo'

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
    projection ≫ ProjectiveLine.toSpec ℂ = toSpec := by
  rw [← parametrization_comp_toSpec, ← Category.assoc, projection_comp_parametrization,
    Category.id_comp]

end AlgebraicGeometry.ComplexConic
