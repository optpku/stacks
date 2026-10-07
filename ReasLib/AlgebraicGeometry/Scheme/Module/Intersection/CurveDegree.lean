module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree

/-!
# Intersection numbers and degrees on curves

This file compares intersection numbers on closed subschemes with the degree of the pulled-back
invertible module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- On a closed subscheme of dimension at most one, the one-factor intersection number of an
invertible module is the curve degree of its pullback. -/
theorem lineNumber_eq_curveDegreeOfInvertible_pullback
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.Modules) [Invertible L]
    (hZdim : topologicalKrullDim Z.subscheme ≤ 1) :
    lineNumber k f Z L =
      (curveDegreeOfInvertible (Z.subschemeι ≫ f) hZdim
        ((Scheme.Modules.pullback Z.subschemeι).obj L) : ℚ) := sorry

/-- On a one-dimensional closed subscheme, the degree with respect to an ample invertible module
is the curve degree of its pullback. -/
theorem degree_eq_curveDegreeOfInvertible_pullback_of_topologicalKrullDim_eq_one
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L] [IsAmple L]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (hZdim : topologicalKrullDim Z.subscheme = 1) :
    degree k f L Z hZdim =
      (curveDegreeOfInvertible (Z.subschemeι ≫ f) hZdim.le
        ((Scheme.Modules.pullback Z.subschemeι).obj L) : ℚ) := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
