/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.Exact
public import ReasLib.Algebra.Module.Finite.Kernel
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Depth bounds for linear maps

This leaf packages the kernel and range forms of the depth lemma for a
single linear map.  It lets homological arguments use a concrete map without
rebuilding its short exact kernel--image row or installing proof-local
finiteness instances.

@stack 00LX
@stack 00LI
@stack 0AV5
-/

@[expose] public section

open scoped ENat

universe u v w

namespace LinearMap

section DepthBounds

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The range of a linear map from a finite module satisfies the quotient-side depth bound. -/
@[stacks 00LX "depth bound for the range of a linear map"]
theorem moduleDepth_range_ge_min (f : M →ₗ[R] N) [Module.Finite R M]
    [Module.Finite R (LinearMap.ker f)] :
    moduleDepth R (LinearMap.range f) ≥
      min (moduleDepth R M) (moduleDepth R (LinearMap.ker f) - 1) := sorry

/-- The kernel of a linear map from a finite module satisfies the submodule-side depth bound. -/
@[stacks 00LX "depth bound for the kernel of a linear map"]
theorem moduleDepth_ker_ge_min (f : M →ₗ[R] N) [Module.Finite R M]
    [Module.Finite R (LinearMap.ker f)] :
    moduleDepth R (LinearMap.ker f) ≥
      min (moduleDepth R M) (moduleDepth R (LinearMap.range f) + 1) := sorry

end DepthBounds

section Surjective

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjective linear map identifies the depth of its range with that of its codomain. -/
@[stacks 00LI "depth of the range of a surjective linear map"]
theorem moduleDepth_range_eq_of_surjective
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    moduleDepth R (LinearMap.range f) = moduleDepth R N := sorry

end Surjective

section Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Lemma 15.23.10 (1): if the finite codomain has depth at least one, then the module of
linear maps from a finite module has depth at least one. -/
@[stacks 0AV5 "Lemma 15.23.10 (1)"]
theorem moduleDepth_ge_one_of_codomain
    (hN : (1 : ℕ∞) ≤ moduleDepth R N) :
    (1 : ℕ∞) ≤ moduleDepth R (M →ₗ[R] N) := sorry

/-- Lemma 15.23.10 (2): if the finite codomain has depth at least two, then the module of
linear maps from a finite module has depth at least two. -/
@[stacks 0AV5 "Lemma 15.23.10 (2)"]
theorem moduleDepth_ge_two_of_codomain
    (hN : (2 : ℕ∞) ≤ moduleDepth R N) :
    (2 : ℕ∞) ≤ moduleDepth R (M →ₗ[R] N) := sorry

end Hom

end LinearMap
