/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite rank after extension to the fraction field

@stack 0FJ8

Over a commutative domain, extending a module to the fraction field preserves `Module.finrank`.
This is the low-level bridge between ordinary module rank and formulas written after generic base
change.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module

/-- Extending a module over a domain to the fraction field preserves its finite rank. -/
@[simp, stacks 0FJ8 "finite rank after generic base change"]
theorem finrank_fractionRing_tensor (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    finrank (FractionRing R) (FractionRing R ⊗[R] M) = finrank R M :=
  (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq

end Module
