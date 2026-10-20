/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.LinearSubspace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

open ProjectiveSpace
open ProjectiveSpace.ClosedSubscheme

/-- A smooth nonplanar curve of degree `d` and genus at least `2` in projective
three-space over an algebraically closed field is hyperelliptic if a linear line
meets it in finitely many distinct points of cardinality `d - 2`. -/
theorem isHyperelliptic_of_secantLine
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    [GeometricallyIrreducible X.hom]
    (ι : X.left ⟶ scheme k 3) [IsClosedImmersion ι]
    (hι : ι ≫ toSpec k 3 = X.hom) {d : ℕ}
    (hdeg : Scheme.Modules.curveDegreeOfInvertible X.hom
        topologicalKrullDim_eq_one.le
        ((Scheme.Modules.pullback ι).obj (twistingSheaf k 3 1)) = (d : ℤ))
    (hgenus : 2 ≤ genus X)
    (h_not_plane : notContainedInPlane ι.ker)
    (h_line : ∃ ℓ : (scheme k 3).IdealSheafData,
      IsLinearLine ℓ ∧
        Finite (Scheme.schemeTheoreticIntersection ι.ker ℓ) ∧
        (Nat.card (Scheme.schemeTheoreticIntersection ι.ker ℓ) : ℤ) = (d : ℤ) - 2) :
    IsHyperelliptic X := sorry

end AlgebraicGeometry.Curve
