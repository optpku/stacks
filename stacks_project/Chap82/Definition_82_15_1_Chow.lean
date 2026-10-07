module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence

/-!
# Chow groups of algebraic spaces

The Chow group of `k`-cycles on a good algebraic space is the quotient of
`Z_k(X)` by rational equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)

/-- The Chow group `CH_k(X)` of `k`-cycles modulo rational equivalence. -/
noncomputable abbrev chowGroup :=
  f.cycleGroup δ k ⧸ RationalEquivalence.boundaries f δ k

/-- The canonical quotient map `Z_k(X) → CH_k(X)`. -/
noncomputable abbrev chowMk : f.cycleGroup δ k →+ f.chowGroup δ k :=
  QuotientAddGroup.mk' (RationalEquivalence.boundaries f δ k)

/-- A cycle has zero Chow class exactly when it is rationally equivalent to
zero. -/
theorem chowMk_eq_zero_iff (α : f.cycleGroup δ k) :
    f.chowMk δ k α = 0 ↔ RationalEquivalence.IsRationallyTrivial f δ k α :=
  sorry

/-- Rational equivalence is equality of Chow classes. -/
theorem rationallyEquivalent_iff_chowMk_eq (α β : f.cycleGroup δ k) :
    RationalEquivalence.RationallyEquivalent f δ k α β ↔
      f.chowMk δ k α = f.chowMk δ k β :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

