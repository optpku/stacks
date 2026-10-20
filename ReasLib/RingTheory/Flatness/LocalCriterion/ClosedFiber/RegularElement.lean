/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Cokernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular Elements on a Closed Fiber

The closed-fiber injectivity criterion specializes to multiplication by an element.  Regularity
of that element modulo the extended maximal ideal then gives both flatness of its principal
quotient and regularity in the target ring.

@stack 00MF
-/

@[expose] public section

open IsLocalRing
open scoped nonZeroDivisors

universe u v

namespace LinearMap.ClosedFiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R]

/-- Multiplication by an element is injective on the closed-fiber quotient when its image there
is regular. -/
@[stacks 00MF "closed-fiber multiplication is injective"]
theorem mul_quotientMap_injective (f : S)
    (hf : IsRegular
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f)) :
    Function.Injective
      (((LinearMap.mul R S) f).quotientMapByIdeal (maximalIdeal R)) := by
  have hf' : Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f ∈
      nonZeroDivisors (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    isRegular_iff_mem_nonZeroDivisors.mp hf
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro a b hab
  have hab' :
      (Submodule.Quotient.mk (f * a) : S ⧸ maximalIdeal R • (⊤ : Submodule R S)) =
        Submodule.Quotient.mk (f * b) := by
    change Submodule.Quotient.mk (((LinearMap.mul R S) f) a) =
      Submodule.Quotient.mk (((LinearMap.mul R S) f) b) at hab
    simpa [mul_comm] using hab
  have hab'' : f * a - f * b ∈ maximalIdeal R • (⊤ : Submodule R S) :=
    (Submodule.Quotient.eq _).1 hab'
  apply (Submodule.Quotient.eq _).2
  rw [Ideal.smul_top_eq_map] at hab'' ⊢
  change f * a - f * b ∈ Ideal.map (algebraMap R S) (maximalIdeal R) at hab''
  change a - b ∈ Ideal.map (algebraMap R S) (maximalIdeal R)
  have hmul : f * (a - b) ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by
    simpa [mul_sub] using hab''
  have hquot_mul_zero :
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) (a - b) *
          Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    simpa [mul_comm] using hmul
  rw [mem_nonZeroDivisors_iff_right] at hf'
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hf' _ hquot_mul_zero)

end LinearMap.ClosedFiber

namespace RingHom.Flat.ClosedFiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

/-- Quotienting by an element that is regular on the closed fiber preserves flatness over the
source ring. -/
@[stacks 00MF "flat principal quotient from a closed-fiber regular element"]
theorem flat_quotient_span_singleton (f : S)
    (hf : IsRegular
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) := by
  let u : S →ₗ[R] S := (LinearMap.mul R S) f
  have hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R)) := by
    simpa [u] using LinearMap.ClosedFiber.mul_quotientMap_injective
      (R := R) (S := S) f hf
  have hrange : LinearMap.range u = (Ideal.span ({f} : Set S)).restrictScalars R := by
    simp [u]
  have hflatRange : Module.Flat R (S ⧸ LinearMap.range u) :=
    LinearMap.ClosedFiber.flat_quotient_range_of_mod_maximalIdeal_injective
      (S := S) u hmod
  rw [hrange] at hflatRange
  let e :
      (S ⧸ Ideal.span ({f} : Set S)) ≃ₗ[R]
        S ⧸ (Ideal.span ({f} : Set S)).restrictScalars R :=
    (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.span ({f} : Set S) : Ideal S)).symm
  exact Module.Flat.of_linearEquiv e

/-- An element regular on the closed-fiber quotient is regular in the target ring. -/
@[stacks 00MF "regular element lifted from the closed fiber"]
theorem isRegular (f : S)
    (hf : IsRegular
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f)) :
    IsRegular f := by
  let u : S →ₗ[R] S := (LinearMap.mul R S) f
  have hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R)) := by
    simpa [u] using LinearMap.ClosedFiber.mul_quotientMap_injective
      (R := R) (S := S) f hf
  have hinj : Function.Injective u :=
    LinearMap.ClosedFiber.injective_of_mod_maximalIdeal_injective (S := S) u hmod
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
  intro x hx
  have hmul_zero : u x = u 0 := by
    simpa [u] using hx
  simpa using hinj hmul_zero

/-- The two conclusions of the regular-element closed-fiber criterion. -/
@[stacks 00MF "flat quotient and regular element"]
theorem flat_quotient_span_singleton_and_isRegular (f : S)
    (hf : IsRegular
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f :=
  ⟨flat_quotient_span_singleton f hf, isRegular f hf⟩

end RingHom.Flat.ClosedFiber
