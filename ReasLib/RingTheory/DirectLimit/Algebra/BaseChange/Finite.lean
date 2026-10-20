/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange

/-!
# Finite module descent along direct-limit base change

This leaf contains the descent consequences controlled by finite generation.
The underlying transport of arbitrary linear maps is owned by
`Ring.DirectLimit.BaseChange`.
-/

@[expose] public section

universe u v w x y

noncomputable section

namespace Ring.DirectLimit

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [IsDirectedOrder I]
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

namespace BaseChange.Finite

/-- Equality of maps out of a finite module after base change to a direct
limit is witnessed after base change to one stage. -/
@[stacks 05LI "finite module base-change descent"]
theorem exists_eq
    {M : Type x} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type y} [AddCommGroup N] [Module A N]
    (u u' : M →ₗ[A] N)
    (h : u.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))) =
      u'.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j)))) :
    ∃ i : I, u.baseChange (R i) = u'.baseChange (R i) := sorry

/-- Surjectivity of the base change of a map onto a finite module is already
witnessed at one stage of a direct limit. -/
@[stacks 05LI "finite module base-change descent"]
theorem exists_surjective
    {M : Type x} [AddCommGroup M] [Module A M]
    {N : Type y} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (u : M →ₗ[A] N)
    (h : Function.Surjective
      (u.baseChange (Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))))) :
    ∃ i : I, Function.Surjective (u.baseChange (R i)) := sorry

end BaseChange.Finite

end Ring.DirectLimit
