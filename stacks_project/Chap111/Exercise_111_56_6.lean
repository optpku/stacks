/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Nodal
import StacksCheckRecall

/-!
# Exercise 111.56.6

For an irreducible degree-`d` plane curve with a unique split node, the
normalization has precisely two branches above the node. The canonical
differential has simple poles there, divisor degree `d(d - 3) - 2`, and
normalization genus `d(d - 3) / 2`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

universe u

/- Exercise 111.56.6 Branch v. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.existsUnique_nodeBranchV :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F),
    ∃! v, IsNodeBranchV d F hF P v)

/- Exercise 111.56.6 Branch w. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.existsUnique_nodeBranchW :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F),
    ∃! w, IsNodeBranchW d F hF P w)

/- Exercise 111.56.6 The fiber over the node. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.nodeBranches_exhaust_fiber :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F)
    {v w : (abstractCurve d F hF).left}
    (hv : IsNodeBranchV d F hF P v) (hw : IsNodeBranchW d F hF P w),
    ∀ q, ((toVanishing d F hF).base q = P ↔ q = v ∨ q = w))

/- Exercise 111.56.6 (1): simple poles at the two branches. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalForm_hasSimplePole_at_nodeBranch :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F)
    {q : (abstractCurve d F hF).left}
    (hq : IsNodeBranchV d F hF P q ∨ IsNodeBranchW d F hF P q)
    (Z : PrimeDivisor (abstractCurve d F hF).left) (hZ : Z.genericPoint = q),
    (canonicalDivisor d F hF).coeff Z = -1)

/- Exercise 111.56.6 (2): degree of the divisor of zeros and poles. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalDivisor_degree_eq :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F),
    (∑ᶠ Z : PrimeDivisor (abstractCurve d F hF).left,
      (canonicalDivisor d F hF).coeff Z) = (d : ℤ) * ((d : ℤ) - 3) - 2)

/- Exercise 111.56.6 (3): genus of the normalization. -/
@[stacks 09U1]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.abstractCurve_genus_eq :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (d : ℕ) (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Fact (Irreducible F)] [IsDomain (affineCoordinateRing F)]
    (hd : 3 ≤ d) (P : Hypersurface.scheme 2 d F hF)
    (hP : (Hypersurface.closedImmersion 2 d F hF).base P = planeNodePoint k)
    (hSing : Sing(Hypersurface.scheme 2 d F hF) = {P}) (hNode : IsNodeExpansion F),
    Scheme.Hom.cohomologyFinrank (abstractCurve d F hF).hom
        (SheafOfModules.unit (abstractCurve d F hF).left.ringCatSheaf) 1 =
      d * (d - 3) / 2)

