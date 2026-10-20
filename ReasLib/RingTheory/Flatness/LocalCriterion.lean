/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.RingTheory.Ideal.Tensor
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.RegularElement

/-!
# Local Flatness Criteria

@stack 00ML
@stack 00ME
@stack 00MF

This leaf owns the ideal-tensor criterion underlying local flatness arguments
for finite modules along a local homomorphism.
-/

@[expose] public section

open scoped Pointwise

universe u v w

namespace Module.Flat

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

include S

/-- Stacks 00ML: a proper quotient with flat induced module and injective ideal tensor
multiplication detects flatness of a finite module over a local homomorphism. -/
@[stacks 00ML "variant local flatness criterion"]
theorem of_quotient_flat_of_ideal_tensorMul_injective
    (I : Ideal R) (hI : I ≠ ⊤)
    (hμ : Function.Injective (I.tensorMul M))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := sorry

omit S

end Module.Flat

namespace LinearMap

section ClosedFiber

variable {R : Type u} {S : Type v} {M N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N]

include S

/-- Stacks 00ME: a linear map from a finite module over a Noetherian local target into a flat
source module is injective when its reduction modulo the source maximal ideal is injective. -/
@[stacks 00ME "closed-fiber injectivity criterion"]
theorem injective_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal R))) :
    Function.Injective u :=
  LinearMap.ClosedFiber.injective_of_mod_maximalIdeal_injective (S := S) u hmod

/-- Stacks 00ME: under the closed-fiber injectivity hypothesis, the quotient by the range of the
linear map is flat over the source local ring. -/
@[stacks 00ME "closed-fiber flat-cokernel criterion"]
theorem flat_quotient_range_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal R))) :
    Module.Flat R (M ⧸ LinearMap.range u) :=
  LinearMap.ClosedFiber.flat_quotient_range_of_mod_maximalIdeal_injective
    (S := S) u hmod

omit S

end ClosedFiber

end LinearMap
