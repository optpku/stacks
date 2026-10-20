/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.StableFree
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
public import ReasLib.RingTheory.Ideal.Nakayama.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting finite stably free modules

@stack 0BC5

This leaf owns the Jacobson-radical lifting statement for finite stably free modules over a
quotient ring.
-/

@[expose] public section

universe u v

namespace Module.StablyFree

/-- Lemma 15.3.3: a finite stably free module over `R ⧸ I` lifts to a finite stably free
`R`-module when `I ≤ Ring.jacobson R`. -/
@[stacks 0BC5 "Lemma 15.3.3"]
theorem exists_lift_of_le_jacobson
    {R : Type u} [Ring R] {I : Ideal R} [I.IsTwoSided]
    {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.Finite (R ⧸ I) E] [Module.StablyFree (R ⧸ I) E]
    (hI : I ≤ Ring.jacobson R) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E),
      Module.Finite R M ∧ Module.StablyFree R M := sorry

end Module.StablyFree
