/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A reduced scheme can have a schematically dense open omitting a weakly associated point. -/
theorem exists_isReduced_denseOpen_missing_weakAss :
    ∃ (X : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsReduced X)
      (U : X.Opens) (x : X),
      AlgebraicGeometry.schemeTheoreticallyDense U ∧ x ∈ X.weakAss ∧ x ∉ U := sorry

end AlgebraicGeometry.Scheme
