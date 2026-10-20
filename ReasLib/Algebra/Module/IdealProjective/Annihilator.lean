/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal

@[expose] public section

/-!
# Annihilators and projective-factor ideals

@stack 0G94

Every scalar acting by zero factors through the zero module.  Consequently the annihilator of a
module is contained in its projective-factor ideal.
-/

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

namespace projectiveFactorIdeal

/-- The annihilator of a module is contained in its projective-factor ideal. -/
@[stacks 0G94 "annihilator bound for the projective-factor ideal"]
theorem annihilator_le :
    annihilator R M ≤ projectiveFactorIdeal R M := sorry

end projectiveFactorIdeal

namespace IsIdealProjective

/-- Lemma 15.71.5: an ideal contained in the annihilator makes the module ideal-projective. -/
@[stacks 0G94 "annihilator criterion for ideal-projectivity"]
theorem of_le_annihilator {I : Ideal R} (h : I ≤ annihilator R M) :
    IsIdealProjective I M := sorry

end IsIdealProjective

end Module
