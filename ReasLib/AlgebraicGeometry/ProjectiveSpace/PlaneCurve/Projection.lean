module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.FunctionField
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RamificationIndex

/-!
# Coordinate projection of plane curves

Projection from the concrete point `(0 : 0 : 1)` is induced by the first two
homogeneous coordinates. For a smooth plane curve avoiding this point, its degree
is the degree of the defining equation, and its ramification is described by the
polar derivative with respect to the third coordinate.
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
    centerPoint k = (centerSection k).base (IsLocalRing.closedPoint k) := rfl

/-- The point `P = (0 : 0 : 1)` lies on the standard chart `D₊(X_2)`. -/
theorem centerPoint_mem_coordinateBasicOpen (k : Type u) [Field k] :
    centerPoint k ∈ infinityChartOpen k := sorry

/-- The coordinate substitution sending the line variables to `X_0` and `X_1`. -/
def projectionCoordinates : Fin 2 → Fin 3 :=
  fun i ↦ i.castSucc

/-- The coordinate substitution of `projectionCoordinates` is `i ↦ i.castSucc`. -/
theorem projectionCoordinates_spec :
    projectionCoordinates = fun i : Fin 2 ↦ i.castSucc := rfl

/-- The ring homomorphism `k[Y_0, Y_1] → k[X_0, X_1, X_2] ⧸ (F)` renaming `Y_i` to the class
of `X_i`. -/
def projectionRingHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 3) k ⧸ (Hypersurface.homogeneousIdeal 2 d F hF).toIdeal :=
  (Ideal.Quotient.mk (Hypersurface.homogeneousIdeal 2 d F hF).toIdeal).comp
    (MvPolynomial.rename projectionCoordinates).toRingHom

/-- The coordinate homomorphism of the projection preserves each homogeneous degree. -/
theorem projectionRingHom_mem {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    {n : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ ProjectiveSpace.grading k 1 n) :
    projectionRingHom d F hF f ∈ Hypersurface.quotientGrading 2 d F hF n := sorry

/-- The graded ring map specifying the projection `(a_0 : a_1 : a_2) ↦ (a_0 : a_1)`. -/
def projectionGradedHom {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    ProjectiveSpace.grading k 1 →+*ᵍ Hypersurface.quotientGrading 2 d F hF where
  toRingHom := projectionRingHom d F hF
  map_mem := projectionRingHom_mem d F hF

/-- If `P = (0 : 0 : 1)` does not lie on `C`, then the graded projection is defined on all of
`C`. -/
theorem projMapDomain_eq_top_of_not_mem_center {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base) :
    projMapDomain (projectionGradedHom d F hF) = ⊤ := sorry

/-- The morphism `π : C ⟶ P^1_k` given by `(a_0 : a_1 : a_2) ↦ (a_0 : a_1)`, defined on all of
`C` once `P = (0 : 0 : 1)` is not a point of `C`. -/
def projection {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base) :
    Hypersurface.scheme 2 d F hF ⟶ ProjectiveSpace.scheme k 1 :=
  projMapOnTarget (projectionGradedHom d F hF)
    (projMapMap (projectionGradedHom d F hF))
    (projMapDomain_eq_top_of_not_mem_center d F hF hP)

/-- The projection is the canonical `Proj` map of `projectionGradedHom` after promoting the
domain to `⊤`. -/
theorem projection_spec {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base) :
    projection d F hF hP =
      projMapOnTarget (projectionGradedHom d F hF)
        (projMapMap (projectionGradedHom d F hF))
        (projMapDomain_eq_top_of_not_mem_center d F hF hP) := rfl

/-- A plane curve over `k` is an integral scheme. -/
instance instIsIntegral_scheme {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))] :
    IsIntegral (Hypersurface.scheme 2 d F hF) :=
  inferInstanceAs (IsIntegral (Over.mk (Hypersurface.hom 2 d F hF)).left)

/-- A plane curve not containing `P = (0 : 0 : 1)` maps dominantly onto `P^1_k` by the
coordinate projection. -/
instance instIsDominant_projection {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base) :
    IsDominant (projection d F hF hP) := sorry

/-- The polar `∂F/∂X_2` of the plane equation `F`. -/
def ramificationEquation {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.pderiv (2 : Fin 3) F

/-- `ramificationEquation F` is the partial derivative of `F` with respect to `X_2`. -/
theorem ramificationEquation_spec {k : Type u} [Field k]
    (F : MvPolynomial (Fin 3) k) :
    ramificationEquation F = MvPolynomial.pderiv (2 : Fin 3) F := rfl

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)

/-- Projection of a smooth degree-`d` plane curve from `(0 : 0 : 1)` outside the curve
has induced function-field degree `d`. -/
theorem projection_degree
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base) :
    (projection d F hF hP).inducedFunctionFieldDegree = d := sorry

/-- Over an algebraically closed field of characteristic different from two, a smooth
degree-`d` plane curve has `d * (d - 1)` index-two closed points under coordinate
projection when every closed-point ramification index is one or two. -/
theorem ramificationPoint_ncard
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base)
    (h_char : (2 : k) ≠ 0)
    (h_ramif : ∀ x : closedPoints (Hypersurface.scheme 2 d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2) :
    Set.ncard {x : closedPoints (Hypersurface.scheme 2 d F hF) |
        (projection d F hF hP).ramificationIndexAt x.1 = 2} =
      d * (d - 1) := sorry

/-- For coordinate projection of a smooth plane curve over an algebraically closed field
of characteristic different from two, with all closed-point ramification indices one
or two, a closed point has index two exactly when its image vanishes on both the
defining form and its third-coordinate polar. -/
theorem ramificationPoint_iff
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base)
    (h_char : (2 : k) ≠ 0)
    (h_ramif : ∀ x : closedPoints (Hypersurface.scheme 2 d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2)
    (x : closedPoints (Hypersurface.scheme 2 d F hF)) :
    (projection d F hF hP).ramificationIndexAt x.1 = 2 ↔
      (Hypersurface.closedImmersion 2 d F hF).base x.1 ∈
        ProjectiveSpectrum.zeroLocus (ProjectiveSpace.grading k 2)
          {F, ramificationEquation F} := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
