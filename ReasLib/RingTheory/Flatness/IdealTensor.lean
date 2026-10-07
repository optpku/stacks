module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# Flatness and Ideal Tensor Multiplication

@stack 00M6

This leaf presents Mathlib's ideal-tensor injectivity criterion for flat modules through the
canonical map `Ideal.tensorMul`.  It is a view layer over the existing flatness API, not a second
definition of flatness.
-/

@[expose] public section

universe u v

namespace Module.Flat

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A flat module makes ideal tensor multiplication injective for every ideal. -/
@[stacks 00M6 "flatness and ideal tensor multiplication"]
theorem tensorMul_injective (hM : Module.Flat R M) (I : Ideal R) :
    Function.Injective (I.tensorMul M) := by
  letI : Module.Flat R M := hM
  rw [Ideal.tensorMul, ← LinearMap.lid_comp_rTensor]
  exact (TensorProduct.lid R M).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

/-- A module is flat exactly when ideal tensor multiplication is injective for every finitely
generated ideal. -/
@[stacks 00M6 "flatness criterion by ideal tensor multiplication"]
theorem iff_tensorMul_injective :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.tensorMul M) := by
  simpa only [Ideal.tensorMul] using
    (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M))

end Module.Flat
