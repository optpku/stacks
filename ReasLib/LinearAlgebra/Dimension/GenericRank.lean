/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.FinitePresentation

@[expose] public section

open scoped TensorProduct

universe u

namespace Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- Cardinal module rank is dimension after extension to the fraction field. -/
theorem rank_fractionRing_tensor (R M : Type u) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    Module.rank (FractionRing R) (FractionRing R ⊗[R] M) = Module.rank R M :=
  (TensorProduct.isBaseChange R M (FractionRing R)).rank_eq

/-- Torsion kernel and cokernel do not change cardinal rank over a domain. -/
theorem rank_eq_of_isTorsion_ker_coker (f : M →ₗ[R] N)
    (hker : IsTorsion R (LinearMap.ker f))
    (hcoker : IsTorsion R (N ⧸ LinearMap.range f)) :
    Module.rank R M = Module.rank R N := sorry

/-- Cardinal rank is additive in a short exact sequence over a domain. -/
theorem rank_eq_add_of_shortExact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Module.rank R N = Module.rank R M + Module.rank R P := sorry

/-- Tensor products multiply cardinal rank, without any finiteness assumption. -/
theorem rank_tensor_of_isDomain (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := sorry

/-- For a finitely presented source, linear Hom multiplies cardinal ranks.
The target module need not be finite. -/
theorem rank_linearMap_of_finitePresentation (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [FinitePresentation R M] :
    Module.rank R (M →ₗ[R] N) = Module.rank R M * Module.rank R N := sorry

/-- Injective extension of domains preserves cardinal rank. -/
theorem rank_baseChange_of_injective (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
    (h : Function.Injective (algebraMap R S)) (M : Type u) [AddCommGroup M] [Module R M] :
    Module.rank S (S ⊗[R] M) = Module.rank R M := sorry

end Module
