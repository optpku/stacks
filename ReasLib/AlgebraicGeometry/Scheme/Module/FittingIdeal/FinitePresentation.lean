/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.RingTheory.FittingIdeal.FinitePresentation

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Fitting ideal sheaf of a finitely presented module is of finite type. -/
theorem fittingIdealSheaf_isFiniteType {S : Scheme.{u}} (ℱ : S.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ) : (fittingIdealSheaf ℱ r).IsFiniteType := sorry

end AlgebraicGeometry.Scheme
