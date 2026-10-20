/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.BaseChange

/-!
# The textbook tensor model for weakly associated primes

@stack 05CC
@stack 0CUB

The canonical scalar-extension owner is `(R ⊗[k] K) ⊗[R] M`. This leaf
provides the source-facing model `M ⊗[k] K` through Mathlib's scoped
right-factor tensor actions. The scopes are deliberately opt-in, so importing
this file never installs competing global algebra or module instances.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right TensorProduct.Right

universe u v w x

namespace weaklyAssociatedPrimes.BaseChange.Textbook

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable [Module k M] [IsScalarTower k R M]

-- Local declaration justification (source-local notation): these aliases retain
-- the two canonical tensor models in the source-facing comparison; the tensor
-- scopes remain explicit and no competing instances are installed here.
local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

/-- The source tensor `M ⊗[k] K` and canonical owner `(R ⊗[k] K) ⊗[R] M`
are canonically isomorphic as additive groups. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
noncomputable def toOwnerAddEquiv : M ⊗[k] K ≃+ Mₖ :=
  ((Algebra.IsPushout.cancelBaseChange k K R Rₖ M).toAddEquiv.trans
    (TensorProduct.comm k K M).toAddEquiv).symm

/-- The canonical tensor comparison respects the scoped
`R ⊗[k] K`-module action on `M ⊗[k] K`. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
theorem toOwnerAddEquiv.map_smul (a : Rₖ) (x : M ⊗[k] K) :
    toOwnerAddEquiv (k := k) (K := K) (R := R) (M := M) (a • x) =
      a • toOwnerAddEquiv (k := k) (K := K) (R := R) (M := M) x := sorry

/-- The source tensor and canonical owner comparison is linear for the scoped
`R ⊗[k] K`-module action on the source tensor. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
noncomputable def toOwner : M ⊗[k] K ≃ₗ[Rₖ] Mₖ :=
  { __ := toOwnerAddEquiv (k := k) (K := K) (R := R) (M := M)
    map_smul' := fun a x =>
      toOwnerAddEquiv.map_smul (k := k) (K := K) (R := R) (M := M) a x }

/-- The tensor comparison sends a source pure tensor to the corresponding
canonical-owner pure tensor. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
theorem toOwner.apply_tmul (m : M) (t : K) :
    toOwner (k := k) (K := K) (R := R) (M := M) (m ⊗ₜ[k] t) =
      ((1 : R) ⊗ₜ[k] t) ⊗ₜ[R] m := sorry

/-- The inverse comparison evaluates a canonical-owner pure tensor in the
source-facing right-tensor model. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
theorem toOwner.symm_tmul (r : R) (t : K) (m : M) :
    (toOwner (k := k) (K := K) (R := R) (M := M)).symm
        ((r ⊗ₜ[k] t) ⊗ₜ[R] m) =
      (r • m) ⊗ₜ[k] t := sorry

/-- The source tensor and canonical owner have the same weakly associated
prime ideals over `R ⊗[k] K`. -/
@[stacks 0CUB "textbook/canonical tensor comparison"]
theorem eq_canonical :
    weaklyAssociatedPrimes Rₖ (M ⊗[k] K) =
      weaklyAssociatedPrimes Rₖ Mₖ := sorry

/-- Lemma 10.66.19 (Tag 0CUB), source-facing form: a weakly associated prime
of `M ⊗[k] K` contracts along a lying-over prime `q` to a weakly associated
prime of `M`. -/
@[stacks 0CUB]
theorem under_mem
    (p : Ideal R) (q : Ideal Rₖ) [q.LiesOver p]
    (hq : q ∈ weaklyAssociatedPrimes Rₖ (M ⊗[k] K)) :
    p ∈ weaklyAssociatedPrimes R M := sorry

end weaklyAssociatedPrimes.BaseChange.Textbook

namespace weaklyAssociatedPrimes.BaseChange.Textbook

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Lemma 10.66.18, tag 05CC: after a flat module is extended from a domain
to its fraction field, weakly associated primes are transported by the
canonical inclusion `S → S ⊗[R] FractionRing R`. -/
@[stacks 05CC "fraction-ring base-change image"]
theorem eq_image_comap_fractionRingBaseChange [Module.Flat R N] :
    weaklyAssociatedPrimes S N =
      Ideal.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            S →+* S ⊗[R] FractionRing R) ''
        weaklyAssociatedPrimes (S ⊗[R] FractionRing R)
          (N ⊗[R] FractionRing R) := sorry

end weaklyAssociatedPrimes.BaseChange.Textbook
