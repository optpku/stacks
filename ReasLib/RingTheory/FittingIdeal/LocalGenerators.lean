/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.RingTheory.FittingIdeal.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fitting ideals and local generators

The `k`th Fitting ideal detects whether a finite module needs at most `k` generators near a
prime, equivalently whether its fiber at that prime has dimension at most `k`.
-/

@[expose] public section

open scoped FittingIdeal TensorProduct

universe u v

namespace FittingIdeal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Noncontainment of `Fit_k(M)` in a prime, the fiber-dimension bound, generation of the
localization by `k` elements, and generation on a standard open neighborhood are equivalent. -/
@[stacks 07ZC "Fitting ideal criterion for local generators"]
theorem not_le_prime_tfae_finrank_and_generators (k : ℕ) (p : Ideal R) [p.IsPrime] :
    List.TFAE
      [ ¬ Fit[R]_(k)(M) ≤ p
      , Module.finrank p.ResidueField (p.ResidueField ⊗[R] M) ≤ k
      , ∃ v : Fin k → LocalizedModule.AtPrime p M,
          Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤
      , ∃ f : R, f ∉ p ∧ ∃ v : Fin k → LocalizedModule.Away f M,
          Submodule.span (Localization.Away f) (Set.range v) = ⊤
      ] := sorry

end FittingIdeal
