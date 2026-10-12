/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A locally Noetherian scheme admitting a coherent sheaf whose degree-zero complex is
dualizing is Cohen-Macaulay. -/
theorem cohenMacaulayOfSingle
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ωX : X.Modules) [ωX.IsCoherent]
    (hωX : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)) :
    Scheme.CohenMacaulay X := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
