/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme Scheme.Hom Scheme.Modules

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a special invertible module on a smooth projective geometrically irreducible curve,
twice the zeroth cohomology finrank is at most the degree plus two. -/
theorem clifford
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (L : X.left.Modules) [Invertible L]
    (h0 : 0 < cohomologyFinrank X.hom L 0)
    (h1 : 0 < cohomologyFinrank X.hom L 1) :
    2 * (cohomologyFinrank X.hom L 0 : ℤ) ≤
      curveDegreeOfInvertible X.hom
        (topologicalKrullDim_eq_one X).le L + 2 := sorry

end AlgebraicGeometry.SchemeOverField
