/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime
public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
public import stacks_project.Chap111.Exercise_111_54_3_Projection
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_Normalization

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

/-- The Fermat equation is `X 0 ^ d + X 1 ^ d - X 2 ^ d`. -/
theorem equation_spec (k : Type u) [Field k] (d : ℕ) :
    equation k d = X (0 : Fin 3) ^ d + X (1 : Fin 3) ^ d - X (2 : Fin 3) ^ d :=
  sorry

/-- The Fermat equation is homogeneous of degree `d` for the standard grading on
`k[T_0, T_1, T_2]`. -/
theorem equation_mem_grading (k : Type u) [Field k] (d : ℕ) :
    equation k d ∈ ProjectiveSpace.grading k 2 d :=
  sorry

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
  PlaneCurve.scheme d (equation k d) (equation_mem_grading k d)

/-- `scheme k d` is the plane curve cut out by `equation k d`. -/
theorem scheme_eq (k : Type u) [Field k] (d : ℕ) :
    scheme k d = PlaneCurve.scheme d (equation k d) (equation_mem_grading k d) :=
  sorry

/-- The Fermat curve as a scheme over `k`. -/
abbrev over (k : Type u) [Field k] (d : ℕ) : SchemeOverField k :=
  PlaneCurve.planeCurveOver d (equation k d) (equation_mem_grading k d)

/-- `over k d` is the over-object of the Fermat curve. -/
theorem over_eq (k : Type u) [Field k] (d : ℕ) :
    over k d = PlaneCurve.planeCurveOver d (equation k d) (equation_mem_grading k d) :=
  sorry

/-- Homogeneous coordinates of the point `p = [1 : 0 : 1]`. -/
def coordsP (k : Type u) [Field k] : Fin 3 → k :=
  ![1, 0, 1]

/-- `coordsP` is the tuple `(1, 0, 1)`. -/
theorem coordsP_spec (k : Type u) [Field k] :
    coordsP k = ![1, 0, 1] :=
  sorry

/-- The tuple `(1, 0, 1)` is nonzero. -/
theorem coordsP_ne_zero (k : Type u) [Field k] : coordsP k ≠ 0 :=
  sorry

/-- Homogeneous coordinates of the point `q = [0 : 1 : 1]`. -/
def coordsQ (k : Type u) [Field k] : Fin 3 → k :=
  ![0, 1, 1]

/-- `coordsQ` is the tuple `(0, 1, 1)`. -/
theorem coordsQ_spec (k : Type u) [Field k] :
    coordsQ k = ![0, 1, 1] :=
  sorry

/-- The tuple `(0, 1, 1)` is nonzero. -/
theorem coordsQ_ne_zero (k : Type u) [Field k] : coordsQ k ≠ 0 :=
  sorry

/-- The Fermat equation vanishes at `[1 : 0 : 1]`. -/
theorem eval_equation_coordsP (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    eval₂Hom (RingHom.id k) (coordsP k) (equation k d) = 0 :=
  sorry

/-- The Fermat equation vanishes at `[0 : 1 : 1]`. -/
theorem eval_equation_coordsQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    eval₂Hom (RingHom.id k) (coordsQ k) (equation k d) = 0 :=
  sorry

/-- Polynomials in the Fermat ideal evaluate to zero in global sections. -/
theorem evalFermatToGamma_ker (k : Type u) [Field k] (d : ℕ) (v : Fin 3 → k)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    ∀ a ∈ (PlaneCurve.homogeneousIdeal d (equation k d) (equation_mem_grading k d)).toIdeal,
      evalToGamma (RingHom.id k) 2 v a = 0 :=
  sorry

/-- Evaluation of the Fermat coordinate ring at a zero of the Fermat equation, as a map
to global sections of `Spec k`. -/
def evalFermatToGamma (k : Type u) [Field k] (d : ℕ) (v : Fin 3 → k)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    MvPolynomial (Fin 3) k ⧸
        (PlaneCurve.homogeneousIdeal d (equation k d) (equation_mem_grading k d)).toIdeal →+*
      Γ(Spec (CommRingCat.of k), ⊤) :=
  Ideal.Quotient.lift
    (PlaneCurve.homogeneousIdeal d (equation k d) (equation_mem_grading k d)).toIdeal
    (evalToGamma (RingHom.id k) 2 v)
    (evalFermatToGamma_ker k d v hker)

/-- `evalFermatToGamma` is the quotient lift of `evalToGamma`. -/
theorem evalFermatToGamma_def (k : Type u) [Field k] (d : ℕ) (v : Fin 3 → k)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    evalFermatToGamma k d v hker =
      Ideal.Quotient.lift
        (PlaneCurve.homogeneousIdeal d (equation k d) (equation_mem_grading k d)).toIdeal
        (evalToGamma (RingHom.id k) 2 v)
        (evalFermatToGamma_ker k d v hker) :=
  sorry

/-- A nonzero zero of the Fermat equation sends the irrelevant ideal onto the unit ideal. -/
theorem evalFermat_map_irrelevant_eq_top (k : Type u) [Field k] (d : ℕ)
    {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    (HomogeneousIdeal.irrelevant
        (PlaneCurve.quotientGrading d (equation k d) (equation_mem_grading k d))).toIdeal.map
      (evalFermatToGamma k d v hker) = ⊤ :=
  sorry

/-- The morphism `Spec k ⟶ X` attached to a nonzero zero of the Fermat equation. -/
def homOfCoords (k : Type u) [Field k] (d : ℕ) {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    Spec (CommRingCat.of k) ⟶ scheme k d :=
  Proj.fromOfGlobalSections
    (PlaneCurve.quotientGrading d (equation k d) (equation_mem_grading k d))
    (evalFermatToGamma k d v hker)
    (evalFermat_map_irrelevant_eq_top k d hv hker)

/-- `homOfCoords` is the projective-spectrum map of Fermat evaluation. -/
theorem homOfCoords_def (k : Type u) [Field k] (d : ℕ) {v : Fin 3 → k} (hv : v ≠ 0)
    (hker : eval₂Hom (RingHom.id k) v (equation k d) = 0) :
    homOfCoords k d hv hker =
      Proj.fromOfGlobalSections
        (PlaneCurve.quotientGrading d (equation k d) (equation_mem_grading k d))
        (evalFermatToGamma k d v hker)
        (evalFermat_map_irrelevant_eq_top k d hv hker) :=
  sorry

/-- The closed point `p = [1 : 0 : 1]` on the Fermat curve. -/
def pointP (k : Type u) [Field k] (d : ℕ) [NeZero d] : scheme k d :=
  (homOfCoords k d (coordsP_ne_zero k) (eval_equation_coordsP k d)).base
    (IsLocalRing.closedPoint k)

/-- `pointP` is the image of the closed point of `Spec k` under the `[1 : 0 : 1]` section. -/
theorem pointP_spec (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointP k d =
      (homOfCoords k d (coordsP_ne_zero k) (eval_equation_coordsP k d)).base
        (IsLocalRing.closedPoint k) :=
  sorry

/-- The point `[1 : 0 : 1]` is a closed point of the Fermat curve. -/
theorem isClosed_singleton_pointP (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsClosed ({pointP k d} : Set (scheme k d)) :=
  sorry

/-- The closed point `q = [0 : 1 : 1]` on the Fermat curve. -/
def pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] : scheme k d :=
  (homOfCoords k d (coordsQ_ne_zero k) (eval_equation_coordsQ k d)).base
    (IsLocalRing.closedPoint k)

/-- `pointQ` is the image of the closed point of `Spec k` under the `[0 : 1 : 1]` section. -/
theorem pointQ_spec (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointQ k d =
      (homOfCoords k d (coordsQ_ne_zero k) (eval_equation_coordsQ k d)).base
        (IsLocalRing.closedPoint k) :=
  sorry

/-- The point `[0 : 1 : 1]` is a closed point of the Fermat curve. -/
theorem isClosed_singleton_pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsClosed ({pointQ k d} : Set (scheme k d)) :=
  sorry

/-- The points `[1 : 0 : 1]` and `[0 : 1 : 1]` on the Fermat curve are distinct. -/
theorem pointP_ne_pointQ (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointP k d ≠ pointQ k d :=
  sorry

/-- The reduced ideal sheaf of the closed point `[1 : 0 : 1]`. -/
def pointPIdealSheaf (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (scheme k d).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨({pointP k d} : Set (scheme k d)), isClosed_singleton_pointP k d⟩

/-- `pointPIdealSheaf` is the vanishing ideal of the singleton `{pointP}`. -/
theorem pointPIdealSheaf_eq (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointPIdealSheaf k d =
      IdealSheafData.vanishingIdeal
        ⟨({pointP k d} : Set (scheme k d)), isClosed_singleton_pointP k d⟩ :=
  sorry

/-- The reduced closed subscheme `{p}` is integral. -/
theorem isIntegral_pointPIdealSheaf_subscheme (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIntegral (pointPIdealSheaf k d).subscheme :=
  sorry

/-- The support of `{p}` is irreducible. -/
theorem isIrreducible_pointPIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIrreducible ((pointPIdealSheaf k d).support : Set (scheme k d)) :=
  sorry

/-- The support of `{p}` has coheight one on the Fermat curve. -/
theorem coheight_pointPIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    Order.coheight
      (⟨((pointPIdealSheaf k d).support : Set (scheme k d)),
          isIrreducible_pointPIdealSheaf_support k d,
          (pointPIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) = 1 :=
  sorry

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
  sorry

/-- The reduced ideal sheaf of the closed point `[0 : 1 : 1]`. -/
def pointQIdealSheaf (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    (scheme k d).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨({pointQ k d} : Set (scheme k d)), isClosed_singleton_pointQ k d⟩

/-- `pointQIdealSheaf` is the vanishing ideal of the singleton `{pointQ}`. -/
theorem pointQIdealSheaf_eq (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    pointQIdealSheaf k d =
      IdealSheafData.vanishingIdeal
        ⟨({pointQ k d} : Set (scheme k d)), isClosed_singleton_pointQ k d⟩ :=
  sorry

/-- The reduced closed subscheme `{q}` is integral. -/
theorem isIntegral_pointQIdealSheaf_subscheme (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIntegral (pointQIdealSheaf k d).subscheme :=
  sorry

/-- The support of `{q}` is irreducible. -/
theorem isIrreducible_pointQIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    IsIrreducible ((pointQIdealSheaf k d).support : Set (scheme k d)) :=
  sorry

/-- The support of `{q}` has coheight one on the Fermat curve. -/
theorem coheight_pointQIdealSheaf_support (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    Order.coheight
      (⟨((pointQIdealSheaf k d).support : Set (scheme k d)),
          isIrreducible_pointQIdealSheaf_support k d,
          (pointQIdealSheaf k d).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (scheme k d)) = 1 :=
  sorry

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
  sorry

/-- Coefficients of the Weil divisor `[p] - [q]`. -/
def divisorCoeff (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    PrimeDivisor (scheme k d) → ℤ :=
  fun Z ↦
    @ite ℤ (Z = pointPPrimeDivisor k d) (Classical.propDecidable _) 1
      (@ite ℤ (Z = pointQPrimeDivisor k d) (Classical.propDecidable _) (-1) 0)

/-- Unfolding of `divisorCoeff` as the two-point characteristic function of `[p]` and `[q]`. -/
theorem divisorCoeff_def (k : Type u) [Field k] (d : ℕ) [NeZero d]
    (Z : PrimeDivisor (scheme k d)) :
    divisorCoeff k d Z =
      @ite ℤ (Z = pointPPrimeDivisor k d) (Classical.propDecidable _) 1
        (@ite ℤ (Z = pointQPrimeDivisor k d) (Classical.propDecidable _) (-1) 0) :=
  sorry

/-- The two-point coefficient function of `[p] - [q]` is locally finite. -/
theorem locallyFinite_divisorCoeff (k : Type u) [Field k] (d : ℕ) [NeZero d] :
    LocallyFinite fun Z : PrimeDivisor (scheme k d) ↦
      if divisorCoeff k d Z = 0 then (∅ : Set (scheme k d))
      else (Z.support : Set (scheme k d)) :=
  sorry

/-- The Weil divisor `D = [p] - [q]` on the Fermat curve. -/
def divisor (k : Type u) [Field k] (d : ℕ) [NeZero d] : WeilDivisor (scheme k d) :=
  WeilDivisor.ofCoeff (scheme k d) (divisorCoeff k d) (locallyFinite_divisorCoeff k d)

/-- Coefficients of `divisor` recover `divisorCoeff`. -/
theorem divisor_coeff (k : Type u) [Field k] (d : ℕ) [NeZero d]
    (Z : PrimeDivisor (scheme k d)) :
    (divisor k d).coeff Z = divisorCoeff k d Z :=
  sorry

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

/-- `lineThroughP` is the linear form `X 0 - X 2`. -/
theorem lineThroughP_spec (k : Type u) [Field k] :
    lineThroughP k = X (0 : Fin 3) - X (2 : Fin 3) :=
  sorry

/-- The line through `p` is homogeneous of degree `1`. -/
theorem lineThroughP_mem_grading (k : Type u) [Field k] :
    lineThroughP k ∈ ProjectiveSpace.grading k 2 1 :=
  sorry

/-- The line `T_1 - T_2 = 0` through `q = [0 : 1 : 1]`. -/
def lineThroughQ (k : Type u) [Field k] : MvPolynomial (Fin 3) k :=
  X (1 : Fin 3) - X (2 : Fin 3)

/-- `lineThroughQ` is the linear form `X 1 - X 2`. -/
theorem lineThroughQ_spec (k : Type u) [Field k] :
    lineThroughQ k = X (1 : Fin 3) - X (2 : Fin 3) :=
  sorry

/-- The line through `q` is homogeneous of degree `1`. -/
theorem lineThroughQ_mem_grading (k : Type u) [Field k] :
    lineThroughQ k ∈ ProjectiveSpace.grading k 2 1 :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.FermatCurve
