/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Split descent of adic formal smoothness

@stack 07EH
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingHom

open Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Lemma 15.37.9 (07EH): adic formal smoothness descends along a base change when the base ring
is an `R`-linear direct summand of the new base ring. -/
@[stacks 07EH "split descent of adic formal smoothness"]
theorem formally_smooth_for_adic_of_split_baseChange
    (𝔫 : Ideal S)
    (hsplit : ∃ σ : R' →ₗ[R] R, Function.LeftInverse σ (Algebra.linearMap R R'))
    (hf : formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫)) :
    formally_smooth_for_adic (algebraMap R S) 𝔫 := sorry

end RingHom
