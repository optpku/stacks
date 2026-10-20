/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.DifferentialExterior
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a smooth proper one-dimensional scheme over a field with bijective
global-sections map, the finrank of global relative differentials equals the genus. -/
theorem differentialFinrank_eq_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Scheme.Hom.cohomologyFinrank X.hom (Ω[X.hom.toShHom]) 0 =
      genus X h_dimension hΓ := sorry

/-- For a smooth proper one-dimensional scheme over a field with bijective
global-sections map, the curve degree of the relative differential module equals
twice the genus minus two. -/
theorem differentialDegree_eq_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Scheme.Modules.curveDegree X.hom h_dimension.le (Ω[X.hom.toShHom]) 1 =
      2 * (genus X h_dimension hΓ : ℤ) - 2 := sorry

end AlgebraicGeometry.SchemeOverField
