module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_AffineChart
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_Normalization

/-!
# Exercise 111.56.6

A nodal plane curve of degree `d ≥ 3` with unique singular point `(1 : 0 : 0)`
and affine expansion `f = xy +` higher-order terms: poles of the canonical form
on the two branches, the degree of its divisor, and the genus of the
normalization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry
open MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- Homogeneous coordinates `(1 : 0 : 0)` of the node in `P^2`. -/
def nodeCoords (k : Type u) [Field k] : Fin 3 → k := ![1, 0, 0]

/-- `nodeCoords k` is the coordinate tuple `![1, 0, 0]`. -/
theorem nodeCoords_spec (k : Type u) [Field k] : nodeCoords k = ![1, 0, 0] := sorry

/-- The node coordinate tuple is nonzero. -/
theorem nodeCoords_ne_zero (k : Type u) [Field k] : nodeCoords k ≠ 0 := sorry

/-- The point `P = (1 : 0 : 0)` of `P^2`, as the image of the closed point of `Spec k`. -/
def planeNodePoint (k : Type u) [Field k] : ProjectiveSpace.scheme k 2 :=
  (ProjectiveSpace.homOf (RingHom.id k)
      (mt (congrArg (fun v : Fin 3 → k ↦ v 0)) one_ne_zero :
        nodeCoords k ≠ 0)).base
    (IsLocalRing.closedPoint k)

/-- `planeNodePoint k` is the image of the closed point of `Spec k` under the morphism
attached to `nodeCoords k`. -/
theorem planeNodePoint_spec (k : Type u) [Field k] :
    planeNodePoint k =
      (ProjectiveSpace.homOf (RingHom.id k) (nodeCoords_ne_zero k)).base
        (IsLocalRing.closedPoint k) := sorry

/-- The affine expansion `f = xy +` higher-order terms at the origin of the `X 0 ≠ 0`
chart: vanishing of degrees `0` and `1`, with quadratic part `X 0 * X 1`. -/
def IsNodeExpansion {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) : Prop :=
  homogeneousComponent 0 (affineEquation F) = 0 ∧
    homogeneousComponent 1 (affineEquation F) = 0 ∧
    homogeneousComponent 2 (affineEquation F) = X (0 : Fin 2) * X 1

/-- Unfold `IsNodeExpansion` into the three homogeneous-component identities. -/
theorem isNodeExpansion_iff {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) :
    IsNodeExpansion F ↔
      homogeneousComponent 0 (affineEquation F) = 0 ∧
        homogeneousComponent 1 (affineEquation F) = 0 ∧
        homogeneousComponent 2 (affineEquation F) = X (0 : Fin 2) * X 1 := sorry

/-- The node branch `v` over `P` characterized by `ord x = 1` and `1 < ord y`. -/
def IsNodeBranchV {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : scheme d F hF) (v : (abstractCurve d F hF).left) : Prop :=
  (toVanishing d F hF).base v = P ∧
    Scheme.ord (standardChartCoord d F hF 0) v = 1 ∧
    1 < Scheme.ord (standardChartCoord d F hF 1) v

/-- Unfold `IsNodeBranchV` into lying over `P` together with the valuation conditions
on the standard chart coordinates. -/
theorem isNodeBranchV_iff {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : scheme d F hF) (v : (abstractCurve d F hF).left) :
    IsNodeBranchV d F hF P v ↔
      (toVanishing d F hF).base v = P ∧
        Scheme.ord (standardChartCoord d F hF 0) v = 1 ∧
        1 < Scheme.ord (standardChartCoord d F hF 1) v := sorry

/-- The node branch `w` over `P` characterized by `1 < ord x` and `ord y = 1`. -/
def IsNodeBranchW {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : scheme d F hF) (w : (abstractCurve d F hF).left) : Prop :=
  (toVanishing d F hF).base w = P ∧
    1 < Scheme.ord (standardChartCoord d F hF 0) w ∧
    Scheme.ord (standardChartCoord d F hF 1) w = 1

/-- Unfold `IsNodeBranchW` into lying over `P` together with the valuation conditions
on the standard chart coordinates. -/
theorem isNodeBranchW_iff {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : scheme d F hF) (w : (abstractCurve d F hF).left) :
    IsNodeBranchW d F hF P w ↔
      (toVanishing d F hF).base w = P ∧
        1 < Scheme.ord (standardChartCoord d F hF 0) w ∧
        Scheme.ord (standardChartCoord d F hF 1) w = 1 := sorry

/-- Under the nodal hypotheses, the normalization has a unique point `v` over `P`
with `ord x = 1` and `1 < ord y`. -/
theorem existsUnique_nodeBranchV {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (hd : 3 ≤ d) (P : scheme d F hF)
    (hP : (closedImmersion d F hF).base P = planeNodePoint k)
    (hSing : Sing(scheme d F hF) = {P}) (hNode : IsNodeExpansion F) :
    ∃! v, IsNodeBranchV d F hF P v := sorry

/-- Under the nodal hypotheses, the normalization has a unique point `w` over `P`
with `1 < ord x` and `ord y = 1`. -/
theorem existsUnique_nodeBranchW {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (hd : 3 ≤ d) (P : scheme d F hF)
    (hP : (closedImmersion d F hF).base P = planeNodePoint k)
    (hSing : Sing(scheme d F hF) = {P}) (hNode : IsNodeExpansion F) :
    ∃! w, IsNodeBranchW d F hF P w := sorry

/-- The normalization of a plane curve is proper over `k`. -/
instance instIsProper_abstractCurve {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (planeCurveOver d F hF)] :
    IsProper (abstractCurve d F hF).hom := sorry

/-- The two node branches are distinct. -/
theorem nodeBranchV_ne_nodeBranchW {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : scheme d F hF) {v w : (abstractCurve d F hF).left}
    (hv : IsNodeBranchV d F hF P v) (hw : IsNodeBranchW d F hF P w) :
    v ≠ w := sorry

/-- Exercise 111.56.6 (1): in Situation 111.56.5, if `d ≥ 3`, the plane curve `D`
has unique singular point `P` mapping to `(1 : 0 : 0)`, and `f = xy +` higher-order
terms at the affine origin, then `canonicalForm` has a first-order pole at each
node branch of `C` over `P`. -/
@[stacks 09U1]
theorem canonicalForm_hasSimplePole_at_nodeBranch {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (hd : 3 ≤ d) (P : scheme d F hF)
    (hP : (closedImmersion d F hF).base P = planeNodePoint k)
    (hSing : Sing(scheme d F hF) = {P}) (hNode : IsNodeExpansion F)
    {q : (abstractCurve d F hF).left}
    (hq : IsNodeBranchV d F hF P q ∨ IsNodeBranchW d F hF P q)
    (Z : PrimeDivisor (abstractCurve d F hF).left) (hZ : Z.genericPoint = q) :
    (canonicalDivisor d F hF).coeff Z = -1 := sorry

/-- Exercise 111.56.6 (2): under the same nodal hypotheses, and using that
`canonicalForm` vanishes to order `d - 3` along the pullback of `X 0 = 0` under
`C ⟶ D`, the degree of the divisor of zeros and poles of `canonicalForm` on `C`
equals `d * (d - 3) - 2`. -/
@[stacks 09U1]
theorem canonicalForm_curveDegree_eq {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (hd : 3 ≤ d) (P : scheme d F hF)
    (hP : (closedImmersion d F hF).base P = planeNodePoint k)
    (hSing : Sing(scheme d F hF) = {P}) (hNode : IsNodeExpansion F) :
    Scheme.Modules.curveDegreeOfInvertible (abstractCurve d F hF).hom
        (topologicalKrullDim_eq_one (abstractCurve d F hF)).le
        (Ω[(abstractCurve d F hF).hom.toShHom]) =
      (d * (d - 3) : ℤ) - 2 := sorry

/-- Exercise 111.56.6 (3): under the same nodal hypotheses, the genus of `C` is
`d * (d - 3) / 2`. -/
@[stacks 09U1]
theorem abstractCurve_genus_eq {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (hd : 3 ≤ d) (P : scheme d F hF)
    (hP : (closedImmersion d F hF).base P = planeNodePoint k)
    (hSing : Sing(scheme d F hF) = {P}) (hNode : IsNodeExpansion F) :
    Scheme.Hom.cohomologyFinrank (abstractCurve d F hF).hom
        (SheafOfModules.unit (abstractCurve d F hF).left.ringCatSheaf) 1 =
      d * (d - 3) / 2 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
