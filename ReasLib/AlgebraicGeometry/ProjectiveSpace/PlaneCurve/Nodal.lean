/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.CanonicalDivisor
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Split nodes on normalized plane curves

The standard split-node expansion determines two valuation-characterized branches
on the normalization. The canonical differential has simple poles on these
branches, yielding the nodal canonical-divisor degree and genus formulas.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry
open MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- Homogeneous coordinates `(1 : 0 : 0)` of the node in `P^2`. -/
def nodeCoords (k : Type u) [Field k] : Fin 3 → k := ![1, 0, 0]

/-- `nodeCoords k` is the coordinate tuple `![1, 0, 0]`. -/
theorem nodeCoords_spec (k : Type u) [Field k] : nodeCoords k = ![1, 0, 0] := rfl

/-- The node coordinate tuple is nonzero. -/
theorem nodeCoords_ne_zero (k : Type u) [Field k] : nodeCoords k ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

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
        (IsLocalRing.closedPoint k) := rfl

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
        homogeneousComponent 2 (affineEquation F) = X (0 : Fin 2) * X 1 := Iff.rfl

/-- The node branch `v` over `P` characterized by `ord x = 1` and `1 < ord y`. -/
def IsNodeBranchV {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : Hypersurface.scheme 2 d F hF) (v : (abstractCurve d F hF).left) : Prop :=
  (toVanishing d F hF).base v = P ∧
    Scheme.ord (standardChartCoord d F hF 0) v = 1 ∧
    1 < Scheme.ord (standardChartCoord d F hF 1) v

/-- Unfold `IsNodeBranchV` into lying over `P` together with the valuation conditions
on the standard chart coordinates. -/
theorem isNodeBranchV_iff {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : Hypersurface.scheme 2 d F hF) (v : (abstractCurve d F hF).left) :
    IsNodeBranchV d F hF P v ↔
      (toVanishing d F hF).base v = P ∧
        Scheme.ord (standardChartCoord d F hF 0) v = 1 ∧
        1 < Scheme.ord (standardChartCoord d F hF 1) v := Iff.rfl

/-- The node branch `w` over `P` characterized by `1 < ord x` and `ord y = 1`. -/
def IsNodeBranchW {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : Hypersurface.scheme 2 d F hF) (w : (abstractCurve d F hF).left) : Prop :=
  (toVanishing d F hF).base w = P ∧
    1 < Scheme.ord (standardChartCoord d F hF 0) w ∧
    Scheme.ord (standardChartCoord d F hF 1) w = 1

/-- Unfold `IsNodeBranchW` into lying over `P` together with the valuation conditions
on the standard chart coordinates. -/
theorem isNodeBranchW_iff {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : Hypersurface.scheme 2 d F hF) (w : (abstractCurve d F hF).left) :
    IsNodeBranchW d F hF P w ↔
      (toVanishing d F hF).base w = P ∧
        1 < Scheme.ord (standardChartCoord d F hF 0) w ∧
        Scheme.ord (standardChartCoord d F hF 1) w = 1 := Iff.rfl

/-- Under the nodal hypotheses, the normalization has a unique point `v` over `P`
with `ord x = 1` and `1 < ord y`. -/
theorem existsUnique_nodeBranchV {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F) :
    ∃! v, IsNodeBranchV d F hF P v := sorry

/-- Under the nodal hypotheses, the normalization has a unique point `w` over `P`
with `1 < ord x` and `ord y = 1`. -/
theorem existsUnique_nodeBranchW {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F) :
    ∃! w, IsNodeBranchW d F hF P w := sorry

/-- The two node branches are distinct. -/
theorem nodeBranchV_ne_nodeBranchW {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [IsDomain (affineCoordinateRing F)] [Curve (planeCurveOver d F hF)]
    (P : Hypersurface.scheme 2 d F hF) {v w : (abstractCurve d F hF).left}
    (hv : IsNodeBranchV d F hF P v) (hw : IsNodeBranchW d F hF P w) :
    v ≠ w := by
  intro h
  subst w
  exact (ne_of_gt hw.2.1) hv.2.1

/-- The two valuation-characterized branches exhaust the normalization fiber
above the unique split node of a plane curve. -/
theorem nodeBranches_exhaust_fiber {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F)
    {v w : (abstractCurve d F hF).left}
    (hv : IsNodeBranchV d F hF P v) (hw : IsNodeBranchW d F hF P w) :
    ∀ q, ((toVanishing d F hF).base q = P ↔ q = v ∨ q = w) := sorry

/-- The canonical differential on the normalization of a plane curve with a unique
split node has a simple pole at either of the two node branches. -/
theorem canonicalForm_hasSimplePole_at_nodeBranch {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F)
    {q : (abstractCurve d F hF).left}
    (hq : IsNodeBranchV d F hF P q ∨ IsNodeBranchW d F hF P q)
    (Z : PrimeDivisor (abstractCurve d F hF).left) (hZ : Z.genericPoint = q) :
    (canonicalDivisor d F hF).coeff Z = -1 := sorry

/-- The degree of the canonical divisor on the normalization of a degree-`d` plane
curve with a unique split node is `d(d - 3) - 2`, expressed as the finite sum of
its prime-divisor coefficients. -/
theorem canonicalDivisor_degree_eq {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F) :
    (∑ᶠ Z : PrimeDivisor (abstractCurve d F hF).left,
      (canonicalDivisor d F hF).coeff Z) = (d : ℤ) * ((d : ℤ) - 3) - 2 := sorry

/-- The genus of the normalization of a degree-`d` plane curve with a unique split
node is `d(d - 3) / 2`. -/
theorem abstractCurve_genus_eq {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F) :
    Scheme.Hom.cohomologyFinrank (abstractCurve d F hF).hom
        (SheafOfModules.unit (abstractCurve d F hF).left.ringCatSheaf) 1 =
      d * (d - 3) / 2 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
