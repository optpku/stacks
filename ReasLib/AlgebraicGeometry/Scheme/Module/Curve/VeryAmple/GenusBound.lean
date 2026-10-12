/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.DegreeTwo
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.GlobalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- On a geometrically integral proper one-dimensional scheme over a field with constant
global functions, an invertible module of degree at least twice the genus plus one is
relatively very ample. -/
@[stacks 0H2V]
theorem relativelyVeryAmple_of_degreeBound
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [GeometricallyIntegral X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (h_degree : 2 * (genus X h_dimension hΓ : ℤ) + 1 ≤
      Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L) :
    RelativelyVeryAmple X.hom L := sorry

end AlgebraicGeometry.SchemeOverField
