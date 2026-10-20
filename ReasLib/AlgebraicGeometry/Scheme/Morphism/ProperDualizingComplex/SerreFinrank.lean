module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.SerrePairing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual

/-!
# Finite-rank Serre duality for invertible modules

This module records the numerical cohomology consequences of Serre duality for
invertible modules on proper Cohen–Macaulay equidimensional curves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- On a proper Cohen–Macaulay equidimensional curve, the zeroth cohomology
finrank of an invertible module equals the first cohomology finrank of its dual
tensored with the curve dualizing module. -/
theorem invertibleModule_h0_finrank_eq_dual_tensor_dualizing_h1
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.CohenMacaulay X.left] [EquidimensionalSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (L : X.left.Modules) [L.Invertible] :
    Scheme.Hom.cohomologyFinrank X.hom L 0 =
      Scheme.Hom.cohomologyFinrank X.hom
        (Scheme.Modules.dual L ⊗ curveDualizingModule X.hom) 1 := sorry

/-- On a proper Cohen–Macaulay equidimensional curve, the first cohomology
finrank of an invertible module equals the zeroth cohomology finrank of its dual
tensored with the curve dualizing module. -/
theorem invertibleModule_h1_finrank_eq_dual_tensor_dualizing_h0
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.CohenMacaulay X.left] [EquidimensionalSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (L : X.left.Modules) [L.Invertible] :
    Scheme.Hom.cohomologyFinrank X.hom L 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (Scheme.Modules.dual L ⊗ curveDualizingModule X.hom) 0 := sorry

end AlgebraicGeometry.Scheme.Hom
