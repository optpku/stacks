/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Colon
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colon Factorization inside Principal Ideals

@stack 05K8
-/

@[expose] public section

universe u

namespace Ideal.IsPrincipal

variable {R : Type u} [CommSemiring R]

/-- A subideal of a principal ideal is the principal ideal times the corresponding colon ideal. -/
@[stacks 05K8 "factorization inside a principal ideal"]
theorem eq_mul_colon_of_le
    {I J : Ideal R} (hJ : J.IsPrincipal) (hIJ : I ≤ J) :
    I = J * (I.colon J) := by
  rcases hJ with ⟨x, rfl⟩
  refine le_antisymm ?_ (Ideal.mul_colon_le I (Ideal.span {x}))
  rw [Ideal.le_span_singleton_mul_iff]
  intro y hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 (hIJ hy)
  exact ⟨z, (Ideal.mem_colon_span_singleton (I := I) (x := x) (r := z)).2 hy,
    mul_comm _ _⟩

/-- For a principal ideal `J`, colon factorization is equivalent to containment in `J`. -/
@[stacks 05K8 "principal colon factorization criterion"]
theorem eq_mul_colon_iff_le
    {I J : Ideal R} (hJ : J.IsPrincipal) :
    I = J * (I.colon J) ↔ I ≤ J := by
  constructor
  · intro h
    rw [h]
    exact Ideal.mul_le_right
  · exact Ideal.IsPrincipal.eq_mul_colon_of_le hJ

end Ideal.IsPrincipal
