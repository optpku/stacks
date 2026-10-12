/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- In dimension one, the dimension-indexed dualizing module is the curve dualizing module. -/
theorem dualizingModule_eq_curveDualizingModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (h_dimension : topologicalKrullDim X = 1) :
    dualizingModule f = curveDualizingModule f := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

namespace AlgebraicGeometry.SchemeOverField

/-- The dimension-indexed dualizing module of a proper Gorenstein equidimensional curve is invertible. -/
instance instDualizingModuleInvertibleOfDimensionOne
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
    [Fact (topologicalKrullDim X.left = 1)] :
    Scheme.Modules.Invertible (dualizingModule X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
