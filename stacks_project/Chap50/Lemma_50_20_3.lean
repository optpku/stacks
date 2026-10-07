module

public import stacks_project.Chap50.Lemma_50_20_1
public import stacks_project.Chap50.Lemma_50_23_8_Differential

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

/-- In degree zero, the zero-extended source of the top Hodge differential is zero. -/
theorem topCohomologySource_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topCohomologySource f 0 = 0 := sorry

/-- In successor degree, the source is the corresponding Hodge cohomology object. -/
theorem topCohomologySource_succ {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    topCohomologySource f (p + 1) =
      hodgeCohomologyObject f p ((p + 1 : ℕ) : ℤ) := sorry

/-- The zero-extended differential from `H^d(X, Ω^(d - 1))` to `H^d(X, Ω^d)`. -/
noncomputable def topCohomologyDifferential {X S : Scheme.{u}} (f : X ⟶ S) :
    (d : ℕ) → topCohomologySource f d ⟶ hodgeCohomologyObject f d (d : ℤ)
  | 0 => 0
  | p + 1 => hodgeDifferential f p (p + 1)

/-- In degree zero, the zero-extended top Hodge differential is the zero morphism. -/
theorem topCohomologyDifferential_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    topCohomologyDifferential f 0 = 0 := sorry

/-- In successor degree, the zero-extended map is the canonical Hodge differential. -/
theorem topCohomologyDifferential_succ {X S : Scheme.{u}}
    (f : X ⟶ S) (p : ℕ) :
    topCohomologyDifferential f (p + 1) =
      hodgeDifferential f p (p + 1) := sorry

/-- Lemma 50.20.3: if `X` is a smooth proper equidimensional `k`-scheme of
dimension `d`, then the zero-extended differential from `H^d(X, Ω^(d - 1))`
to `H^d(X, Ω^d)` is zero. -/
@[stacks 0FW6]
theorem topCohomologyDifferential_eq_zero {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [IsProper X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (h_dimension : topologicalKrullDim X.left = d) :
    topCohomologyDifferential X.hom d = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham
