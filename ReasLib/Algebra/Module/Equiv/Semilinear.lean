/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Linear views of semilinear equivalences

This leaf contains the small scalar-transport bridge that is useful whenever a module is
identified with a module over a ring-equivalent target.  The target module is equipped with the
pulled-back action by `Module.compHom`; the underlying additive equivalence then becomes an
ordinary linear equivalence over the source ring.
-/

noncomputable section

universe u v w z

namespace LinearEquiv

variable {R : Type u} {S : Type v} {M : Type w} {N : Type z}
variable [Semiring R] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module S N]

/-- Regard a semilinear equivalence as a linear equivalence after pulling the target action back
along its ring equivalence.  This is the canonical owner for the otherwise repeated
consumer-local `Module.compHom` construction. -/
@[stacks 052N "semilinear equivalence under pulled-back scalars"]
noncomputable def ofSemilinear
    (e : R ≃+* S)
    (f : @LinearEquiv R S _ _ (e : R →+* S) (e.symm : S →+* R)
      (RingHomInvPair.of_ringEquiv e)
      (RingHomInvPair.of_ringEquiv_symm e) M N _ _ _ _) :
    -- Local instance justification (defeq pin): the linear target uses the explicitly transported
    -- action, rather than any unrelated `Module R N` instance.
    let _ : Module R N := Module.compHom N (e : R →+* S)
    M ≃ₗ[R] N :=
by
  letI := Module.compHom N (e : R →+* S)
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.of_ringEquiv_symm e
  exact f.toAddEquiv.toLinearEquiv (fun r x ↦ f.map_smulₛₗ r x)

/-- The linear view has the same underlying function as the original semilinear equivalence. -/
@[simp, stacks 052N "semilinear equivalence linear view application"]
theorem ofSemilinear_apply
    (e : R ≃+* S)
    (f : @LinearEquiv R S _ _ (e : R →+* S) (e.symm : S →+* R)
      (RingHomInvPair.of_ringEquiv e)
      (RingHomInvPair.of_ringEquiv_symm e) M N _ _ _ _) (x : M) :
    ofSemilinear e f x = f x := sorry

end LinearEquiv
