/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Proetale

/-- The étale precoverage is contained in the pro-étale precoverage. -/
theorem etalePrecoverage_le_proetalePrecoverage :
    AlgebraicGeometry.Scheme.etalePrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.proetalePrecoverage.{u} := sorry

/-- The Zariski precoverage is contained in the pro-étale precoverage. -/
theorem zariskiPrecoverage_le_proetalePrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.proetalePrecoverage.{u} := sorry

end AlgebraicGeometry.Scheme.Proetale
