/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSeries

/-- On a proper curve with only constant global functions, the dimension of a linear series is at
most its degree. -/
theorem dimension_le_degree
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) {d r : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r) : r ≤ d := sorry

/-- If a linear series of positive degree on a proper curve with only constant global functions
has dimension equal to its degree, then the first cohomology of the structure sheaf is zero.

The statement of Stacks tag `0CCS` omits positivity, which is needed for the ampleness step in
its proof. The trivial linear series of degree and dimension zero on an elliptic curve is a
counterexample without this hypothesis. -/
theorem structureSheafH1_isZero_of_dimension_eq_degree
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) {d r : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r) (h_eq : r = d)
    (hd : 0 < d) :
    IsZero (Scheme.Hom.cohomology X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1) := sorry

/-- If a linear series of positive degree on a proper curve with only constant global functions
has dimension equal to its degree, then the curve has genus zero.

As in `structureSheafH1_isZero_of_dimension_eq_degree`, positivity corrects the omission in
Stacks tag `0CCS` and excludes the trivial linear series on a curve of positive genus. -/
theorem genus_eq_zero_of_dimension_eq_degree
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) {d r : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d r) (h_eq : r = d)
    (hd : 0 < d) :
    SchemeOverField.genus X (topologicalKrullDim_eq_one X) hΓ = 0 := sorry

end AlgebraicGeometry.LinearSeries
