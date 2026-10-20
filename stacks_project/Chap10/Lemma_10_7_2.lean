/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.7.2

@stack 00GJ
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S]

namespace Module.Finite

@[stacks 00GJ "restriction-of-scalars direction"]
#check @Module.Finite.of_restrictScalars_finite
@[stacks 00GJ "finite transitivity direction"]
#check @Module.Finite.trans

-- Lemma 10.7.2: the source equivalence packages the two canonical directions above.
@[stacks 00GJ]
#check
  (show Module.Finite R M ↔ Module.Finite S M from
    ⟨fun _ ↦ of_restrictScalars_finite R S M, fun _ ↦ trans S M⟩)

end Module.Finite
