/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap111.Exercise_111_54_3_Hypersurface

/-!
# Coordinate projection of a plane curve from (0 : 0 : 1)

This module owns the point `P = (0 : 0 : 1)` in `P^2_k`, the graded coordinate projection
`(a_0 : a_1 : a_2) ↦ (a_0 : a_1)`, and the polar `∂F/∂X_2`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The standard affine chart `D₊(X_2)` on `P^2_k`. -/
abbrev infinityChart (k : Type u) [Field k] : (ProjectiveSpace.scheme k 2).affineOpens :=
  ProjectiveSpace.coordinateBasicOpen 2 (2 : Fin 3)

/-- The standard chart `D₊(X_2)` as an open subset of `P^2_k`. -/
abbrev infinityChartOpen (k : Type u) [Field k] : (ProjectiveSpace.scheme k 2).Opens :=
  infinityChart k

/-- The section of `P^2_k` induced by the origin of the standard `D₊(X_2)` chart. -/
def centerSection (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ ProjectiveSpace.scheme k 2 :=
  AffineSpace.homOfVector (𝟙 _) (fun _ : ULift.{u} (Fin 2) ↦ 0) ≫
    (ProjectiveSpace.CoordinateChart.iso 2 (2 : Fin 3) :
        (infinityChartOpen k).toScheme ≅
          𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).inv ≫
      (infinityChartOpen k).ι

/-- The point `P = (0 : 0 : 1)` of `P^2_k`, as the image of the closed point of `Spec k`
under `centerSection k`. -/
def centerPoint (k : Type u) [Field k] : ProjectiveSpace.scheme k 2 :=
  (centerSection k).base (IsLocalRing.closedPoint k)

/-- `centerPoint k` is the image of the closed point of `Spec k` under the `D₊(X_2)`-origin
section. -/
theorem centerPoint_spec (k : Type u) [Field k] :
    centerPoint k = (centerSection k).base (IsLocalRing.closedPoint k) := sorry

/-- The point `P = (0 : 0 : 1)` lies on the standard chart `D₊(X_2)`. -/
theorem centerPoint_mem_coordinateBasicOpen (k : Type u) [Field k] :
    centerPoint k ∈ infinityChartOpen k := sorry

/-- The coordinate substitution sending the line variables to `X_0` and `X_1`. -/
def projectionCoordinates : Fin 2 → Fin 3 :=
  fun i ↦ i.castSucc

/-- The coordinate substitution of `projectionCoordinates` is `i ↦ i.castSucc`. -/
theorem projectionCoordinates_spec :
    projectionCoordinates = fun i : Fin 2 ↦ i.castSucc := sorry

/-- The ring homomorphism `k[Y_0, Y_1] → k[X_0, X_1, X_2] ⧸ (F)` renaming `Y_i` to the class
of `X_i`. -/
def projectionRingHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 3) k ⧸ (homogeneousIdeal d F hF).toIdeal :=
  (Ideal.Quotient.mk (homogeneousIdeal d F hF).toIdeal).comp
    (MvPolynomial.rename projectionCoordinates).toRingHom

/-- The coordinate homomorphism of the projection preserves each homogeneous degree. -/
theorem projectionRingHom_mem {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    {n : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ ProjectiveSpace.grading k 1 n) :
    projectionRingHom d F hF f ∈ quotientGrading d F hF n := sorry

/-- The graded ring map specifying the projection `(a_0 : a_1 : a_2) ↦ (a_0 : a_1)`. -/
def projectionGradedHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    ProjectiveSpace.grading k 1 →+*ᵍ quotientGrading d F hF where
  toRingHom := projectionRingHom d F hF
  map_mem := projectionRingHom_mem d F hF

/-- If `P = (0 : 0 : 1)` does not lie on `C`, then the graded projection is defined on all of
`C`. -/
theorem projMapDomain_eq_top_of_not_mem_center {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base) :
    projMapDomain (projectionGradedHom d F hF) = ⊤ := sorry

/-- The morphism `π : C ⟶ P^1_k` given by `(a_0 : a_1 : a_2) ↦ (a_0 : a_1)`, defined on all of
`C` once `P = (0 : 0 : 1)` is not a point of `C`. -/
def projection {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base) :
    scheme d F hF ⟶ ProjectiveSpace.scheme k 1 :=
  projMapOnTarget (projectionGradedHom d F hF)
    (projMapMap (projectionGradedHom d F hF))
    (projMapDomain_eq_top_of_not_mem_center d F hF hP)

/-- The projection is the canonical `Proj` map of `projectionGradedHom` after promoting the
domain to `⊤`. -/
theorem projection_spec {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base) :
    projection d F hF hP =
      projMapOnTarget (projectionGradedHom d F hF)
        (projMapMap (projectionGradedHom d F hF))
        (projMapDomain_eq_top_of_not_mem_center d F hF hP) := sorry

/-- A plane curve over `k` is an integral scheme. -/
instance instIsIntegral_scheme {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (hom d F hF))] :
    IsIntegral (scheme d F hF) :=
  inferInstanceAs (IsIntegral (Over.mk (hom d F hF)).left)

/-- A plane curve not containing `P = (0 : 0 : 1)` maps dominantly onto `P^1_k` by the
coordinate projection. -/
instance instIsDominant_projection {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (hom d F hF))]
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base) :
    IsDominant (projection d F hF hP) := sorry

/-- The polar `∂F/∂X_2` of the plane equation `F`. -/
def ramificationEquation {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.pderiv (2 : Fin 3) F

/-- `ramificationEquation F` is the partial derivative of `F` with respect to `X_2`. -/
theorem ramificationEquation_spec {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) :
    ramificationEquation F = MvPolynomial.pderiv (2 : Fin 3) F := sorry

/-- For a positive-degree form, the polar `∂F/∂X_2` is homogeneous of degree `d - 1`. -/
theorem ramificationEquation_mem_grading {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hd : 0 < d) :
    ramificationEquation F ∈ ProjectiveSpace.grading k 2 (d - 1) := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve

