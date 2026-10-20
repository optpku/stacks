/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Product.Finite
public import ReasLib.Algebra.Module.Product.Projective
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Finite Projective Modules over Product Semirings

This leaf combines the separate finite-generation and projectivity criteria for modules over a
product semiring.
-/

@[expose] public section

universe u v w

namespace Module.FiniteProjective

variable (R : Type u) (S : Type v) [Semiring R] [Semiring S]

/-- A module over a product semiring is finite projective exactly when its two idempotent factors
are finite projective over the corresponding factors. -/
@[stacks 00JH "finite projective product semiring module criterion"]
theorem product_iff (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module.FiniteProjective (R × S) M ↔
      Module.FiniteProjective R (Module.Product.leftSubmodule R S M) ∧
        Module.FiniteProjective S (Module.Product.rightSubmodule R S M) := by
  constructor
  · rintro ⟨hfinite, hprojective⟩
    have hfactors := (Module.Product.finite_iff R S M).mp hfinite
    have hprojectiveFactors := (Module.Projective.product_iff R S M).mp hprojective
    exact ⟨⟨hfactors.1, hprojectiveFactors.1⟩, ⟨hfactors.2, hprojectiveFactors.2⟩⟩
  · rintro ⟨⟨hfiniteLeft, hprojectiveLeft⟩, ⟨hfiniteRight, hprojectiveRight⟩⟩
    exact ⟨(Module.Product.finite_iff R S M).mpr ⟨hfiniteLeft, hfiniteRight⟩,
      (Module.Projective.product_iff R S M).mpr ⟨hprojectiveLeft, hprojectiveRight⟩⟩

end Module.FiniteProjective
