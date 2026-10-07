module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import ReasLib.Algebra.Category.ModuleCat.Tor.EulerCharacteristic

/-!
# Intersection multiplicity of modules

This module records finiteness, dimension, vanishing, and positivity properties
of the Tor Euler characteristic over a regular local ring.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable (M N : ModuleCat.{u} R)
  [hM_finite : Module.Finite R M] [hN_finite : Module.Finite R N]
  [hM_nontrivial : Nontrivial M] [hN_nontrivial : Nontrivial N]
variable (h_support :
  Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆ {IsLocalRing.closedPoint R})

include hM_finite hN_finite hM_nontrivial hN_nontrivial h_support

/-- Every Tor module has finite length when the tensor product of two nonzero
finite modules is supported at the closed point. -/
theorem length_ne_top_of_tensorSupport (p : ℕ) :
    Module.length R (obj p M N) ≠ ⊤ := sorry

/-- The Tor modules of two nonzero finite modules over a regular local ring
vanish in all sufficiently large degrees. -/
theorem eventuallyIsZero_of_regularLocal : EventuallyIsZero M N := sorry

/-- The sum of the support dimensions of two nonzero finite modules whose
tensor product is supported at the closed point is at most the ring dimension. -/
theorem supportDim_add_le :
    Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R := sorry

/-- The Tor Euler characteristic vanishes when the sum of support dimensions
is strictly less than the dimension of the regular local ring. -/
theorem eulerCharacteristic_eq_zero_of_supportDim_add_lt
    (h_dim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    eulerCharacteristic M N = 0 := sorry

/-- The Tor Euler characteristic of two nonzero finite modules whose tensor
product is supported at the closed point is nonnegative. -/
theorem eulerCharacteristic_nonneg : 0 ≤ eulerCharacteristic M N := sorry

/-- If a regular local ring contains a field and the support dimensions have
the expected sum, then the Tor Euler characteristic is positive. -/
theorem eulerCharacteristic_pos_of_field {k : Type u} [Field k] [Algebra k R]
    (h_dim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < eulerCharacteristic M N := sorry

end CategoryTheory.ModuleCat.Tor
