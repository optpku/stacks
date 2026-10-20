/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic.Secant
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

open AlgebraicGeometry.Curve AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/- Exercise 111.61.3: over an algebraically closed field `k`, a smooth curve
`X ⊂ scheme k 3` of degree `d` and genus at least `2` that is not contained in a
plane, and that meets some linear line in `d - 2` distinct points,
is hyperelliptic. -/
@[stacks 0ELI] #check (AlgebraicGeometry.Curve.isHyperelliptic_of_secantLine :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
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
        (Nat.card (Scheme.schemeTheoreticIntersection ι.ker ℓ) : ℤ) = (d : ℤ) - 2),
    IsHyperelliptic X)
