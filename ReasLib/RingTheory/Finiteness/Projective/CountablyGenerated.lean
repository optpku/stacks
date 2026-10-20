/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Countably generated projective modules

This leaf owns the conjunction of countable generation and projectivity, parallel to
`Module.FiniteProjective`, together with its elementary projections and scalar extension.

@stack 058Y
@stack 0590
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module

/-- An `R`-module is countably generated projective when it is both countably generated and
projective. -/
@[stacks 058Y "countably generated projective modules"]
def CountablyGeneratedProjective (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] : Prop :=
  Module.CountablyGenerated R M ∧ Module.Projective R M

namespace CountablyGeneratedProjective

section Basic

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Countably generated projectivity includes countable generation. -/
theorem countablyGenerated (hM : CountablyGeneratedProjective R M) :
    Module.CountablyGenerated R M := sorry

/-- Countably generated projectivity includes projectivity. -/
theorem projective (hM : CountablyGeneratedProjective R M) :
    Module.Projective R M := sorry

end Basic

section BaseChange

variable {R : Type u} {S : Type w} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Scalar extension preserves countably generated projectivity. -/
theorem baseChange (hM : CountablyGeneratedProjective R M) :
    CountablyGeneratedProjective S (S ⊗[R] M) := sorry

end BaseChange

end CountablyGeneratedProjective

namespace Projective

variable {R : Type u} [Ring R]

/-- Theorem 10.84.5 (Kaplansky): every projective module is an internal direct sum of countably
generated projective submodules. -/
@[stacks 058Y "Kaplansky decomposition"]
theorem exists_countablyGenerated_decomposition
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P] :
    ∃ (ι : Type w) (summand : ι → Submodule R P),
      iSupIndep summand ∧ iSup summand = ⊤ ∧
        ∀ i, Module.CountablyGeneratedProjective R (summand i) := sorry

/-- Lemma 10.85.1: every projective `R`-module is free if and only if every
countably generated projective `R`-module is free. -/
@[stacks 0590]
theorem all_free_iff_all_countablyGenerated_free :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.Free R P) ↔
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.CountablyGenerated R P → Module.Free R P) := sorry

end Projective

end Module
