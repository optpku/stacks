/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.RingTheory.KrullDimension.Polynomial.PrincipalQuotient

/-!
# Fermat plane curves of degree `d`

The homogeneous Fermat equation `T_0 ^ d + T_1 ^ d - T_2 ^ d` in `P^2`, its `Proj`
model, the rational points `p = [1 : 0 : 1]` and `q = [0 : 1 : 1]`, and the Weil
divisor `[p] - [q]`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FermatCurve

/-- The homogeneous Fermat equation `T_0 ^ d + T_1 ^ d - T_2 ^ d` in three variables. -/
def equation (k : Type u) [Field k] (d : ℕ) : MvPolynomial (Fin 3) k :=
  X (0 : Fin 3) ^ d + X (1 : Fin 3) ^ d - X (2 : Fin 3) ^ d

/-- The Fermat equation is homogeneous of degree `d` for the standard grading on
`k[T_0, T_1, T_2]`. -/
theorem equation_mem_grading (k : Type u) [Field k] (d : ℕ) :
    equation k d ∈ ProjectiveSpace.grading k 2 d :=
  by
  exact ((isHomogeneous_X_pow (0 : Fin 3) d).add
    (isHomogeneous_X_pow (1 : Fin 3) d)).sub (isHomogeneous_X_pow (2 : Fin 3) d)

/-- Over a field of characteristic zero, a positive-degree Fermat equation is irreducible. -/
theorem irreducible_equation (k : Type u) [Field k] [CharZero k] (d : ℕ) [NeZero d] :
    Irreducible (equation k d) :=
  sorry

/-- Irreducibility of a positive-degree Fermat equation, as a `Fact`. -/
instance instFactIrreducible_equation (k : Type u) [Field k] [CharZero k] (d : ℕ) [NeZero d] :
    Fact (Irreducible (equation k d)) :=
  ⟨irreducible_equation k d⟩

/-- The Fermat curve `X : T_0 ^ d + T_1 ^ d - T_2 ^ d = 0 ⊂ P^2_k`. -/
abbrev scheme (k : Type u) [Field k] (d : ℕ) : Scheme.{u} :=
  Hypersurface.scheme 2 d (equation k d) (equation_mem_grading k d)

/-- The Fermat curve as a scheme over `k`. -/
abbrev over (k : Type u) [Field k] (d : ℕ) : SchemeOverField k :=
  Over.mk (Hypersurface.hom 2 d (equation k d) (equation_mem_grading k d))

/-- Homogeneous coordinates of the point `p = [1 : 0 : 1]`. -/
def coordsP (k : Type u) [Field k] : Fin 3 → k :=
  ![1, 0, 1]

/-- The tuple `(1, 0, 1)` is nonzero. -/
theorem coordsP_ne_zero (k : Type u) [Field k] : coordsP k ≠ 0 :=
  by
  intro h
  have := congrFun h (0 : Fin 3)
  simpa [coordsP] using this

/-- Homogeneous coordinates of the point `q = [0 : 1 : 1]`. -/
def coordsQ (k : Type u) [Field k] : Fin 3 → k :=
  ![0, 1, 1]

/-- The tuple `(0, 1, 1)` is nonzero. -/
theorem coordsQ_ne_zero (k : Type u) [Field k] : coordsQ k ≠ 0 :=
  by
  intro h
  have := congrFun h (1 : Fin 3)
  simpa [coordsQ] using this

/-- The Fermat equation vanishes at `[1 : 0 : 1]`. -/
theorem eval_equation_coordsP (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    eval₂Hom (RingHom.id k) (coordsP k) (equation k d) = 0 :=
  by
  simp [equation, coordsP, NeZero.ne d]

/-- The Fermat equation vanishes at `[0 : 1 : 1]`. -/
theorem eval_equation_coordsQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    eval₂Hom (RingHom.id k) (coordsQ k) (equation k d) = 0 :=
  by
  simp [equation, coordsQ, NeZero.ne d]

/-- Polynomials in the Fermat ideal evaluate to zero in global sections. -/
theorem evalFermatToGamma_ker (k : Type u) [Field k] (d : ℕ) (v : Fin 3 → k)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    ∀ a ∈ (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d)).toIdeal,
      evalToGamma (RingHom.id k) 2 v a = 0 :=
  by
  change Ideal.span {equation k d} ≤ RingHom.ker (evalToGamma (RingHom.id k) 2 v)
  rw [Ideal.span_singleton_le_iff_mem]
  change (Scheme.ΓSpecIso (.of k)).inv.hom (eval₂Hom (RingHom.id k) v (equation k d)) = 0
  rw [hker, map_zero]

/-- Evaluation of the Fermat coordinate ring at a zero of the Fermat equation, as a map
to global sections of `Spec k`. -/
def evalFermatToGamma (k : Type u) [Field k] (d : ℕ) (v : Fin 3 → k)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    MvPolynomial (Fin 3) k ⧸
        (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d)).toIdeal →+*
      Γ(Spec (CommRingCat.of k), ⊤) :=
  Ideal.Quotient.lift
    (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d)).toIdeal
    (evalToGamma (RingHom.id k) 2 v)
    (evalFermatToGamma_ker k d v hker)

/-- A nonzero zero of the Fermat equation sends the irrelevant ideal onto the unit ideal. -/
theorem evalFermat_map_irrelevant_eq_top (k : Type u) [Field k] (d : ℕ)
    {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    (HomogeneousIdeal.irrelevant
        (Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d))).toIdeal.map
      (evalFermatToGamma k d v hker) = ⊤ :=
  by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  let J := (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d)).toIdeal
  have hm : Ideal.Quotient.mk J (X i) ∈
      (HomogeneousIdeal.irrelevant (Hypersurface.quotientGrading 2 d (equation k d)
        (equation_mem_grading k d))).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (GradedAlgebra.Quotient.mk_mem_grading _ J (isHomogeneous_X k i))
  have hu : IsUnit (evalFermatToGamma k d v hker (Ideal.Quotient.mk J (X i))) := by
    change IsUnit ((Scheme.ΓSpecIso (.of k)).inv.hom (eval₂Hom (RingHom.id k) v (X i)))
    simpa using ((isUnit_iff_ne_zero.mpr hi).map (Scheme.ΓSpecIso (.of k)).inv.hom)
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hm) hu

/-- The morphism `Spec k ⟶ X` attached to a nonzero zero of the Fermat equation. -/
def homOfCoords (k : Type u) [Field k] (d : ℕ) {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    Spec (CommRingCat.of k) ⟶ scheme k d :=
  Proj.fromOfGlobalSections
    (Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d))
    (evalFermatToGamma k d v hker)
    (evalFermat_map_irrelevant_eq_top k d hv hker)

private abbrev quotientCoordinate (k : Type u) [Field k] (d : ℕ) (i : Fin 3) :=
  Ideal.Quotient.mk (Hypersurface.homogeneousIdeal 2 d (equation k d)
    (equation_mem_grading k d)).toIdeal (X i)

private abbrev quotientChartRing (k : Type u) [Field k] (d : ℕ) :=
  HomogeneousLocalization.Away
    (Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d))
    (quotientCoordinate k d 2)

private abbrev quotientChartMap (k : Type u) [Field k] (d : ℕ) :
    coordinateAway (R := k) 2 2 →+* quotientChartRing k d :=
  HomogeneousLocalization.Away.map
    (projQuotientGradedHom (grading k 2)
      (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d))) (X 2)

private theorem quotientChartMap_surjective (k : Type u) [Field k] (d : ℕ) :
    Function.Surjective (quotientChartMap k d) := by
  intro z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d))
    (GradedAlgebra.Quotient.mk_mem_grading _ _ (isHomogeneous_X k (2 : Fin 3))) z
  obtain ⟨p, hp⟩ := GradedAlgebra.Quotient.exists_rep_of_mem_grading (grading k 2)
    (Hypersurface.homogeneousIdeal 2 d (equation k d) (equation_mem_grading k d)).toIdeal ⟨a, ha⟩
  refine ⟨HomogeneousLocalization.Away.mk (grading k 2) (isHomogeneous_X k (2 : Fin 3))
    m p.val p.property, ?_⟩
  apply HomogeneousLocalization.val_injective
  simp [quotientChartMap, HomogeneousLocalization.Away.map, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, projQuotientGradedHom, hp]

private abbrev affineEquation (k : Type u) [Field k] (d : ℕ) : MvPolynomial (Fin 2) k :=
  dehomogenizeAt 2 (2 : Fin 3) (Equiv.refl (Fin 2)) (equation k d)

private abbrev affineChartMap (k : Type u) [Field k] (d : ℕ) :
    MvPolynomial (Fin 2) k →+* quotientChartRing k d :=
  (quotientChartMap k d).comp (affineChartHom (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2)))

set_option backward.isDefEq.respectTransparency false in
private theorem affineChartMap_ker (k : Type u) [Field k] (d : ℕ) :
    RingHom.ker (affineChartMap k d) = Ideal.span {affineEquation k d} := by
  let F := equation k d
  let J := (Hypersurface.homogeneousIdeal 2 d F (equation_mem_grading k d)).toIdeal
  let D := dehomogenizeAt (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2))
  have hl (a : MvPolynomial (Fin 3) k) (m : ℕ) (ha : a ∈ grading k 2 (m • 1)) :
      CoordinateChart.dehomogenization (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2))
        (HomogeneousLocalization.Away.mk (grading k 2) (isHomogeneous_X k (2 : Fin 3))
          m a ha) = D a := by
    change Localization.awayLift D (X 2) (dehomogenizeAt_coordinate_isUnit _ _ _)
      (Localization.mk a ⟨X 2 ^ m, m, rfl⟩) = D a
    simpa using Localization.awayLift_mk D (X 2) a 1 (by simp [D]) m
  apply le_antisymm
  · intro p hp
    obtain ⟨m, a, ha, he⟩ := HomogeneousLocalization.Away.mk_surjective (grading k 2)
      (isHomogeneous_X k (2 : Fin 3))
      (affineChartHom (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2)) p)
    have hp' : D a = p := by
      have h := congrArg (CoordinateChart.dehomogenization (R := k) 2 (2 : Fin 3)
        (Equiv.refl (Fin 2))) he
      rw [hl] at h
      simpa only [← RingHom.comp_apply, CoordinateChart.dehomogenization_comp_affineChartHom,
        RingHom.id_apply] using h
    change quotientChartMap k d _ = 0 at hp
    rw [← he] at hp
    have hv := congrArg HomogeneousLocalization.val hp
    simp only [quotientChartMap, HomogeneousLocalization.Away.map,
      HomogeneousLocalization.Away.mk, HomogeneousLocalization.val_zero,
      projQuotientGradedHom, GradedRingHom.coe_mk] at hv
    change Localization.mk (Ideal.Quotient.mk J a)
      (⟨quotientCoordinate k d 2 ^ m, m, rfl⟩ :
        Submonoid.powers (quotientCoordinate k d 2)) = 0 at hv
    rw [← Localization.mk_zero (1 : Submonoid.powers (quotientCoordinate k d 2)),
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hv
    simp only [OneMemClass.coe_one, mul_zero] at hv
    obtain ⟨⟨_, t, rfl⟩, ht⟩ := hv
    have hj : X (2 : Fin 3) ^ t * a ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, map_pow, one_mul] using ht
    have hmem := Ideal.mem_map_of_mem D hj
    have hmap : J.map D = Ideal.span {affineEquation k d} := by
      rw [show J = Ideal.span {F} from rfl, Ideal.map_span, Set.image_singleton]
    rw [hmap] at hmem
    simpa [D, map_mul, map_pow, hp'] using hmem
  · rw [Ideal.span_singleton_le_iff_mem]
    let z := HomogeneousLocalization.Away.mk (grading k 2) (isHomogeneous_X k (2 : Fin 3))
      d F (by simpa using equation_mem_grading k d)
    have hz : CoordinateChart.dehomogenization (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2)) z =
        affineEquation k d := hl F d (by simpa using equation_mem_grading k d)
    change affineChartMap k d (affineEquation k d) = 0
    rw [← hz]
    change quotientChartMap k d
      (((affineChartHom (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2))).comp
        (CoordinateChart.dehomogenization (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2)))) z) = 0
    rw [CoordinateChart.affineChartHom_comp_dehomogenization]
    apply HomogeneousLocalization.val_injective
    have hfq : Ideal.Quotient.mk J F = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp only [RingHom.id_apply, z, quotientChartMap, HomogeneousLocalization.Away.map,
      HomogeneousLocalization.Away.mk, projQuotientGradedHom, GradedRingHom.coe_mk,
      HomogeneousLocalization.val_zero]
    change Localization.mk (Ideal.Quotient.mk J F) _ = 0
    rw [hfq]
    exact Localization.mk_zero _


private def quotientChartEquiv (k : Type u) [Field k] (d : ℕ) :
    (MvPolynomial (Fin 2) k ⧸ Ideal.span {affineEquation k d}) ≃+* quotientChartRing k d :=
  (Ideal.quotEquivOfEq (affineChartMap_ker k d).symm).trans
    ((affineChartMap k d).quotientKerEquivOfSurjective
      ((quotientChartMap_surjective k d).comp
        (CoordinateChart.ringEquiv (R := k) 2 (2 : Fin 3) (Equiv.refl (Fin 2))).symm.surjective))

private theorem affineEquation_eq (k : Type u) [Field k] (d : ℕ) :
    affineEquation k d = X (0 : Fin 2) ^ d + X (1 : Fin 2) ^ d - 1 := by
  simp [affineEquation, equation, dehomogenizeAt]
  congr 2

private theorem affineEquation_ne_zero (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    affineEquation k d ≠ 0 := by
  intro h
  have := congrArg (eval₂Hom (RingHom.id k) (fun _ : Fin 2 ↦ 0)) h
  simpa [affineEquation_eq, NeZero.ne d] using this

private theorem affineEquation_not_isUnit (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    ¬ IsUnit (affineEquation k d) := by
  intro h
  have h' := h.map (eval₂Hom (RingHom.id k) (![1, 0] : Fin 2 → k))
  simpa [affineEquation_eq, NeZero.ne d] using h'

private theorem quotient_maximal_height {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} (h0 : f ≠ 0) (hu : ¬ IsUnit f)
    (M : Ideal (MvPolynomial (Fin 2) k ⧸ Ideal.span {f})) [M.IsMaximal] :
    M.height = 1 := by
  let q := Ideal.Quotient.mk (Ideal.span {f})
  let N := M.comap q
  have : N.IsMaximal := Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective
  let e : MvPolynomial (Fin 2) k ≃+* Polynomial (Polynomial k) :=
    ((finSuccEquiv k 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv k (Fin 1)))).toRingEquiv
  let N' := N.map e
  have : N'.IsMaximal := Ideal.map_isMaximal_of_equiv e
  have : (N'.under (Polynomial k)).IsMaximal :=
    Polynomial.isMaximal_comap_C_of_isJacobsonRing N'
  have hn : N.height = 2 := by
    rw [← e.height_map N, Polynomial.height_eq_height_add_one (N'.under (Polynomial k)) N',
      IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField k)]
    rfl
  have hmem : f ∈ N := by
    change q f ∈ M
    simp [q, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))]
  have hl := Ideal.height_le_height_add_one_of_mem hmem
  rw [hn, show N.map q = M from M.map_comap_of_surjective q Ideal.Quotient.mk_surjective] at hl
  have hupp := Ideal.height_le_ringKrullDim_of_ne_top (I := M) Ideal.IsPrime.ne_top'
  rw [ringKrullDim_quotient_span_singleton_eq_one_of_ne_zero_not_isUnit h0 hu] at hupp
  have hupp' : M.height ≤ 1 := by exact_mod_cast hupp
  exact le_antisymm hupp' ((ENat.add_le_add_iff_right (by simp)).mp hl)


private abbrev quotientChartOpen (k : Type u) [Field k] (d : ℕ) : (scheme k d).Opens :=
  Proj.basicOpen
    (Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d))
    (quotientCoordinate k d 2)

private def quotientChartIso (k : Type u) [Field k] (d : ℕ) :
    (quotientChartOpen k d).toScheme ≅
      Spec (.of (MvPolynomial (Fin 2) k ⧸ Ideal.span {affineEquation k d})) :=
  Proj.basicOpenIsoSpec _ (quotientCoordinate k d 2)
    (GradedAlgebra.Quotient.mk_mem_grading _ _ (isHomogeneous_X k (2 : Fin 3)))
    Nat.zero_lt_one ≪≫ Scheme.Spec.mapIso (quotientChartEquiv k d).toCommRingCatIso.op

set_option backward.isDefEq.respectTransparency false in
private theorem point_mem_quotientChartOpen (k : Type u) [Field k] (d : ℕ)
    {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) (hv2 : v 2 = 1) :
    (homOfCoords k d hv hker).base (IsLocalRing.closedPoint k) ∈ quotientChartOpen k d := by
  have he : homOfCoords k d hv hker ⁻¹ᵁ quotientChartOpen k d =
      (Spec (.of k)).basicOpen (evalFermatToGamma k d v hker (quotientCoordinate k d 2)) :=
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
      (GradedAlgebra.Quotient.mk_mem_grading _ _ (isHomogeneous_X k (2 : Fin 3)))
  change IsLocalRing.closedPoint k ∈ homOfCoords k d hv hker ⁻¹ᵁ quotientChartOpen k d
  rw [he]
  simp [evalFermatToGamma, evalToGamma, quotientCoordinate, hv2]

set_option backward.isDefEq.respectTransparency false in
private theorem coheight_of_closed_in_quotientChart (k : Type u) [Field k] (d : ℕ) [NeZero d]
    (x : scheme k d) (hx : IsClosed ({x} : Set (scheme k d)))
    (hchart : x ∈ quotientChartOpen k d) : Order.coheight x = 1 := by
  let y : (quotientChartOpen k d).toScheme := ⟨x, hchart⟩
  let e := quotientChartIso k d
  let z := e.hom.base y
  have hz : IsClosed ({z} : Set (Spec (.of (MvPolynomial (Fin 2) k ⧸
      Ideal.span {affineEquation k d})))) := by
    have hy : IsClosed ({y} : Set (quotientChartOpen k d).toScheme) := by
      have he : ({y} : Set (quotientChartOpen k d).toScheme) =
          (Subtype.val : (quotientChartOpen k d) → scheme k d) ⁻¹' {x} := by
        ext a
        change a = ⟨x, hchart⟩ ↔ a.val = x
        exact Subtype.ext_iff
      rw [he]
      exact hx.preimage (quotientChartOpen k d).isOpenEmbedding.continuous
    convert e.hom.isClosedEmbedding.isClosedMap _ hy using 1
    exact (Set.image_singleton : e.hom.base '' {y} = {z}).symm
  have : z.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hz
  have hh := quotient_maximal_height (affineEquation_ne_zero k d)
    (affineEquation_not_isUnit k d) z.asIdeal
  rw [idealHeight_eq_coheight] at hh
  rw [show x = (quotientChartOpen k d).ι.base y from rfl,
    coheight_eq_of_isOpenImmersion]
  rw [← coheight_eq_of_isOpenImmersion e.hom]
  exact hh


/-- The closed point `p = [1 : 0 : 1]` on the Fermat curve. -/
def pointP (k : Type u) [Field k] (d : ℕ) [NeZero d] : scheme k d :=
  (homOfCoords k d (coordsP_ne_zero k) (eval_equation_coordsP k d)).base
    (IsLocalRing.closedPoint k)

/-- The point `[1 : 0 : 1]` is a closed point of the Fermat curve. -/
theorem isClosed_singleton_pointP (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsClosed ({pointP k d} : Set (scheme k d)) := by
  let G := Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d)
  let t : scheme k d ⟶ Spec (.of k) :=
    Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap k (G 0)))
  have he : homOfCoords k d (coordsP_ne_zero k) (eval_equation_coordsP k d) ≫ t =
      𝟙 (Spec (.of k)) := by
    dsimp only [t]
    rw [homOfCoords, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
      Category.assoc, ← Spec.map_comp]
    convert toSpecΓ_SpecMap_ΓSpecIso_inv (.of k) using 2
    congr 1
    ext r
    change (evalFermatToGamma k d (coordsP k) (eval_equation_coordsP k d))
      (Ideal.Quotient.mk _ (MvPolynomial.C r)) = (Scheme.ΓSpecIso (.of k)).inv.hom r
    simp [evalFermatToGamma, evalToGamma]
  have hc := isClosedImmersion_of_comp_eq_id t _ he
  have hr : Set.range (homOfCoords k d (coordsP_ne_zero k)
      (eval_equation_coordsP k d)) = {pointP k d} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg _ (Subsingleton.elim x
        (IsLocalRing.closedPoint k)))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint k, rfl⟩
  rw [← hr]
  exact (homOfCoords k d (coordsP_ne_zero k)
    (eval_equation_coordsP k d)).isClosedEmbedding.isClosed_range

/-- The closed point `q = [0 : 1 : 1]` on the Fermat curve. -/
def pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] : scheme k d :=
  (homOfCoords k d (coordsQ_ne_zero k) (eval_equation_coordsQ k d)).base
    (IsLocalRing.closedPoint k)

/-- The point `[0 : 1 : 1]` is a closed point of the Fermat curve. -/
theorem isClosed_singleton_pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsClosed ({pointQ k d} : Set (scheme k d)) := by
  let G := Hypersurface.quotientGrading 2 d (equation k d) (equation_mem_grading k d)
  let t : scheme k d ⟶ Spec (.of k) :=
    Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap k (G 0)))
  have he : homOfCoords k d (coordsQ_ne_zero k) (eval_equation_coordsQ k d) ≫ t =
      𝟙 (Spec (.of k)) := by
    dsimp only [t]
    rw [homOfCoords, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
      Category.assoc, ← Spec.map_comp]
    convert toSpecΓ_SpecMap_ΓSpecIso_inv (.of k) using 2
    congr 1
    ext r
    change (evalFermatToGamma k d (coordsQ k) (eval_equation_coordsQ k d))
      (Ideal.Quotient.mk _ (MvPolynomial.C r)) = (Scheme.ΓSpecIso (.of k)).inv.hom r
    simp [evalFermatToGamma, evalToGamma]
  have hc := isClosedImmersion_of_comp_eq_id t _ he
  have hr : Set.range (homOfCoords k d (coordsQ_ne_zero k)
      (eval_equation_coordsQ k d)) = {pointQ k d} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg _ (Subsingleton.elim x
        (IsLocalRing.closedPoint k)))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint k, rfl⟩
  rw [← hr]
  exact (homOfCoords k d (coordsQ_ne_zero k)
    (eval_equation_coordsQ k d)).isClosedEmbedding.isClosed_range

/-- The points `[1 : 0 : 1]` and `[0 : 1 : 1]` on the Fermat curve are distinct. -/
theorem pointP_ne_pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointP k d ≠ pointQ k d :=
  sorry

/-- The reduced ideal sheaf of the closed point `[1 : 0 : 1]`. -/
def pointPIdealSheaf (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (scheme k d).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨({pointP k d} : Set (scheme k d)), isClosed_singleton_pointP k d⟩

/-- The reduced closed subscheme `{p}` is integral. -/
theorem isIntegral_pointPIdealSheaf_subscheme (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIntegral (pointPIdealSheaf k d).subscheme := by
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
  refine ⟨?_, IdealSheafData.vanishingIdeal_subscheme_isReduced _⟩
  apply ((pointPIdealSheaf k d).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff).mpr
  apply Subtype.irreducibleSpace
  rw [IdealSheafData.range_subschemeι, pointPIdealSheaf,
    IdealSheafData.support_vanishingIdeal]
  exact isIrreducible_singleton

/-- The support of `{p}` is irreducible. -/
theorem isIrreducible_pointPIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIrreducible ((pointPIdealSheaf k d).support : Set (scheme k d)) := by
  simp only [pointPIdealSheaf, IdealSheafData.support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_mk]
  exact isIrreducible_singleton

/-- The support of `{p}` has coheight one on the Fermat curve. -/
theorem coheight_pointPIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    Order.coheight
      (⟨((pointPIdealSheaf k d).support : Set (scheme k d)),
          isIrreducible_pointPIdealSheaf_support k d,
          (pointPIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) = 1 := by
  have he : (⟨((pointPIdealSheaf k d).support : Set (scheme k d)),
      isIrreducible_pointPIdealSheaf_support k d,
      (pointPIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) =
      irreducibleSetEquivPoints.symm (pointP k d) := by
    apply TopologicalSpace.IrreducibleCloseds.ext
    simp [pointPIdealSheaf, IdealSheafData.support_vanishingIdeal,
      (isClosed_singleton_pointP k d).closure_eq]
  rw [he, Order.coheight_orderIso]
  exact coheight_of_closed_in_quotientChart k d (pointP k d)
    (isClosed_singleton_pointP k d)
    (point_mem_quotientChartOpen k d (coordsP_ne_zero k)
      (eval_equation_coordsP k d) (by simp [coordsP]))

/-- The prime divisor `[p]` on the Fermat curve. -/
def pointPPrimeDivisor (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    PrimeDivisor (scheme k d) :=
  PrimeDivisor.ofIdeal (scheme k d) (pointPIdealSheaf k d)
    (isIntegral_pointPIdealSheaf_subscheme k d)
    (isIrreducible_pointPIdealSheaf_support k d)
    (coheight_pointPIdealSheaf_support k d)

/-- The ideal sheaf of `[p]` is the vanishing ideal of `{p}`. -/
theorem pointPPrimeDivisor_ideal (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (pointPPrimeDivisor k d).ideal = pointPIdealSheaf k d :=
  by
  rfl

/-- The reduced ideal sheaf of the closed point `[0 : 1 : 1]`. -/
def pointQIdealSheaf (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (scheme k d).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨({pointQ k d} : Set (scheme k d)), isClosed_singleton_pointQ k d⟩

/-- The reduced closed subscheme `{q}` is integral. -/
theorem isIntegral_pointQIdealSheaf_subscheme (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIntegral (pointQIdealSheaf k d).subscheme := by
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
  refine ⟨?_, IdealSheafData.vanishingIdeal_subscheme_isReduced _⟩
  apply ((pointQIdealSheaf k d).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff).mpr
  apply Subtype.irreducibleSpace
  rw [IdealSheafData.range_subschemeι, pointQIdealSheaf,
    IdealSheafData.support_vanishingIdeal]
  exact isIrreducible_singleton

/-- The support of `{q}` is irreducible. -/
theorem isIrreducible_pointQIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIrreducible ((pointQIdealSheaf k d).support : Set (scheme k d)) := by
  simp only [pointQIdealSheaf, IdealSheafData.support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_mk]
  exact isIrreducible_singleton

/-- The support of `{q}` has coheight one on the Fermat curve. -/
theorem coheight_pointQIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    Order.coheight
      (⟨((pointQIdealSheaf k d).support : Set (scheme k d)),
          isIrreducible_pointQIdealSheaf_support k d,
          (pointQIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) = 1 := by
  have he : (⟨((pointQIdealSheaf k d).support : Set (scheme k d)),
      isIrreducible_pointQIdealSheaf_support k d,
      (pointQIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) =
      irreducibleSetEquivPoints.symm (pointQ k d) := by
    apply TopologicalSpace.IrreducibleCloseds.ext
    simp [pointQIdealSheaf, IdealSheafData.support_vanishingIdeal,
      (isClosed_singleton_pointQ k d).closure_eq]
  rw [he, Order.coheight_orderIso]
  exact coheight_of_closed_in_quotientChart k d (pointQ k d)
    (isClosed_singleton_pointQ k d)
    (point_mem_quotientChartOpen k d (coordsQ_ne_zero k)
      (eval_equation_coordsQ k d) (by simp [coordsQ]))

/-- The prime divisor `[q]` on the Fermat curve. -/
def pointQPrimeDivisor (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    PrimeDivisor (scheme k d) :=
  PrimeDivisor.ofIdeal (scheme k d) (pointQIdealSheaf k d)
    (isIntegral_pointQIdealSheaf_subscheme k d)
    (isIrreducible_pointQIdealSheaf_support k d)
    (coheight_pointQIdealSheaf_support k d)

/-- The ideal sheaf of `[q]` is the vanishing ideal of `{q}`. -/
theorem pointQPrimeDivisor_ideal (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (pointQPrimeDivisor k d).ideal = pointQIdealSheaf k d :=
  by
  rfl

/-- Coefficients of the Weil divisor `[p] - [q]`. -/
def divisorCoeff (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    PrimeDivisor (scheme k d) → ℤ :=
  fun Z ↦
    @ite ℤ (Z = pointPPrimeDivisor k d) (Classical.propDecidable _) 1
      (@ite ℤ (Z = pointQPrimeDivisor k d) (Classical.propDecidable _) (-1) 0)

/-- The two-point coefficient function of `[p] - [q]` is locally finite. -/
theorem locallyFinite_divisorCoeff (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    LocallyFinite fun Z : PrimeDivisor (scheme k d) ↦
      if divisorCoeff k d Z = 0 then (∅ : Set (scheme k d))
      else (Z.support : Set (scheme k d)) :=
  by
  classical
  intro x
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  apply (Set.toFinite ({pointPPrimeDivisor k d, pointQPrimeDivisor k d} : Set _)).subset
  intro Z hZ
  by_contra h
  have hp : Z ≠ pointPPrimeDivisor k d := fun he ↦ h (by simp [he])
  have hq : Z ≠ pointQPrimeDivisor k d := fun he ↦ h (by simp [he])
  simpa [divisorCoeff, hp, hq] using hZ

/-- The Weil divisor `D = [p] - [q]` on the Fermat curve. -/
def divisor (k : Type u) [Field k] (d : ℕ) [NeZero d] : WeilDivisor (scheme k d) :=
  WeilDivisor.ofCoeff (scheme k d) (divisorCoeff k d) (locallyFinite_divisorCoeff k d)

/-- Coefficients of `divisor` recover `divisorCoeff`. -/
theorem divisor_coeff (k : Type u) [Field k] (d : ℕ) [NeZero d]
    (Z : PrimeDivisor (scheme k d)) :
    (divisor k d).coeff Z = divisorCoeff k d Z :=
  by
  rfl

/-- The coefficient of `[p]` in `D = [p] - [q]` is `1`. -/
theorem divisor_coeff_pointP (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (divisor k d).coeff (pointPPrimeDivisor k d) = 1 :=
  sorry

/-- The coefficient of `[q]` in `D = [p] - [q]` is `-1`. -/
theorem divisor_coeff_pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (divisor k d).coeff (pointQPrimeDivisor k d) = -1 :=
  sorry

/-- The line `T_0 - T_2 = 0` through `p = [1 : 0 : 1]`. -/
def lineThroughP (k : Type u) [Field k] : MvPolynomial (Fin 3) k :=
  X (0 : Fin 3) - X (2 : Fin 3)

/-- The line through `p` is homogeneous of degree `1`. -/
theorem lineThroughP_mem_grading (k : Type u) [Field k] :
    lineThroughP k ∈ ProjectiveSpace.grading k 2 1 :=
  by
  exact (isHomogeneous_X k (0 : Fin 3)).sub (isHomogeneous_X k (2 : Fin 3))

/-- The line `T_1 - T_2 = 0` through `q = [0 : 1 : 1]`. -/
def lineThroughQ (k : Type u) [Field k] : MvPolynomial (Fin 3) k :=
  X (1 : Fin 3) - X (2 : Fin 3)

/-- The line through `q` is homogeneous of degree `1`. -/
theorem lineThroughQ_mem_grading (k : Type u) [Field k] :
    lineThroughQ k ∈ ProjectiveSpace.grading k 2 1 :=
  by
  exact (isHomogeneous_X k (1 : Fin 3)).sub (isHomogeneous_X k (2 : Fin 3))


/-- The divisor of the difference of the two distinguished points has nonzero Weil divisor class
over an algebraically closed field of characteristic zero, for degree at least three. -/
@[stacks 0G17]
theorem divisorClass_ne_zero {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)] :
    weilDivisorClassGroupMk (scheme k d) (divisor k d) ≠ 0 :=
  sorry

/-- The degree times the divisor of the difference of the two distinguished points has zero
Weil divisor class over an algebraically closed field of characteristic zero. -/
@[stacks 0G17]
theorem nsmul_divisorClass_eq_zero {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)] :
    weilDivisorClassGroupMk (scheme k d) (d • divisor k d) = 0 :=
  sorry

/-- The multiple `d D` is a principal Weil divisor on the Fermat curve. -/
theorem nsmul_divisor_isPrincipal {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)] :
    IsPrincipalWeilDivisor (scheme k d) (d • divisor k d) :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.FermatCurve
