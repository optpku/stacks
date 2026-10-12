/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion Ideals of Module Elements

This leaf extends Mathlib's elementwise `Ideal.torsionOf` API with functorial
behavior under injective linear maps.  It is independent of associated-prime
theory and is therefore owned at the module-torsion layer.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- An injective linear map preserves the torsion ideal of every module element. -/
@[stacks 0548 "torsion transport under an injective map"]
theorem torsionOf_map_eq_of_injective {f : M →ₗ[R] N}
    (hf : Function.Injective f) (m : M) :
    torsionOf R N (f m) = torsionOf R M m := by
  ext r
  rw [mem_torsionOf_iff, mem_torsionOf_iff]
  constructor
  · intro hr
    exact hf (by simpa using hr)
  · intro hr
    simpa using congrArg f hr

end Ideal
