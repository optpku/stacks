/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Projective

@[expose] public section

/-!
# Projective-factor ideals

For an `R`-module `M`, the scalars whose action on `M` factors through a projective module form
an ideal of `R`.  This ideal is the canonical owner of ideal-projectivity: an ideal `I` makes `M`
ideal-projective precisely when `I` is contained in it.

The ideal-valued API records more information than the original pointwise predicate and makes
monotonicity, comparison, annihilator, and duality results ordinary ideal inclusions.

@stack 0G93
-/

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The ideal of scalars whose action on `M` factors through a projective module. -/
@[stacks 0G93 "projective-factor ideal"]
def projectiveFactorIdeal (R : Type u) (M : Type v) [CommSemiring R]
    [AddCommMonoid M] [Module R M] : Ideal R :=
  (LinearMap.projectiveFactors (R := R) (M := M) (N := M)).comap (LinearMap.lsmul R M)

/-- Membership in `projectiveFactorIdeal` is projective factorisation of the scalar action. -/
theorem mem_projectiveFactorIdeal (a : R) :
    a ∈ projectiveFactorIdeal R M ↔
      (LinearMap.lsmul R M a).FactorsThroughProjective := sorry

/-- An ideal `I` makes `M` ideal-projective when all its scalar actions factor through
projective modules. -/
@[stacks 0G93 "ideal-projective module"]
def IsIdealProjective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  I ≤ projectiveFactorIdeal R M

/-- The pointwise factorisation criterion for ideal-projectivity. -/
theorem isIdealProjective_iff (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughProjective := sorry

namespace IsIdealProjective

variable {I J : Ideal R}

/-- An ideal-projectivity hypothesis gives membership in the projective-factor ideal. -/
theorem mem_projectiveFactorIdeal (h : IsIdealProjective I M) {a : R} (ha : a ∈ I) :
    a ∈ projectiveFactorIdeal R M := sorry

/-- An ideal-projectivity hypothesis gives the structured projective factorisation of each
scalar action. -/
theorem factorisation (h : IsIdealProjective I M) (a : I) :
    Nonempty (LinearMap.Factorisation.Projective (LinearMap.lsmul R M (a : R))) := sorry

/-- Compatibility view of an ideal-projectivity hypothesis as an explicit projective
factorisation.  New code should normally use `factorisation` or ideal membership instead. -/
theorem factorsThroughProjective (h : IsIdealProjective I M) (a : I) :
    ∃ (P : Type (max u v)) (_ : AddCommMonoid P) (_ : Module R P)
      (_ : Module.Projective R P) (i : M →ₗ[R] P) (r : P →ₗ[R] M),
      LinearMap.lsmul R M (a : R) = r.comp i := sorry

/-- Ideal-projectivity is contravariantly monotone in the ideal. -/
theorem mono (h : IsIdealProjective I M) (hJI : J ≤ I) : IsIdealProjective J M := sorry

/-- Every module is ideal-projective for the zero ideal. -/
theorem zero (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective (⊥ : Ideal R) M := sorry

/-- A projective module is ideal-projective for every ideal. -/
theorem of_projective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    [Module.Projective R M] : IsIdealProjective I M := sorry

/-- Projectivity is the top-ideal case of ideal-projectivity. -/
theorem top_iff (M : Type v) [AddCommMonoid M] [Module R M] :
    IsIdealProjective (⊤ : Ideal R) M ↔ Module.Projective R M := sorry

end IsIdealProjective

namespace projectiveFactorIdeal

/-- The projective-factor ideal is the top ideal exactly for projective modules. -/
@[stacks 0G93 "projectivity detected by the projective-factor ideal"]
theorem eq_top_iff (M : Type v) [AddCommMonoid M] [Module R M] :
    projectiveFactorIdeal R M = ⊤ ↔ Module.Projective R M := sorry

end projectiveFactorIdeal

end Module
