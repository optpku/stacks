/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Hodge
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology.Differential

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The zero-extended source `H^d(X, Ω^(d - 1))` of the top Hodge differential. -/
noncomputable def topCohomologySource {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) → coefficientModules f
  | 0 => 0
  | p + 1 => hodgeCohomologyObject f p ((p + 1 : ℕ) : ℤ)

/-- The zero-extended differential from `H^d(X, Ω^(d - 1))` to `H^d(X, Ω^d)`. -/
noncomputable def topCohomologyDifferential {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) → topCohomologySource f d ⟶ hodgeCohomologyObject f d (d : ℤ)
  | 0 => 0
  | p + 1 => hodgeDifferential f p (p + 1)

/-- For a smooth proper equidimensional scheme of dimension `d` over a field, the
zero-extended differential from `H^d(X, Ω^(d - 1))` to `H^d(X, Ω^d)` is zero. -/
theorem topCohomologyDifferential_eq_zero {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [IsProper X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (h_dimension : topologicalKrullDim X.left = d) :
    topCohomologyDifferential X.hom d = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham
