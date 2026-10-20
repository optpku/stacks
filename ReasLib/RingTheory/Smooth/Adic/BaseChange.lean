/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-!
# Base change of adic formal smoothness

@stack 07EG
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingHom

section

open Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Lemma 15.37.8: adic formal smoothness is stable under arbitrary base change. -/
@[stacks 07EG "base change of adic formal smoothness"]
theorem formally_smooth_for_adic_baseChange
    (𝔫 : Ideal S) (hf : formally_smooth_for_adic (algebraMap R S) 𝔫) :
    formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫) := sorry

end

end RingHom
