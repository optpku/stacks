/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Modules over principal square-zero extensions

For a chosen generator `g` of the kernel of a square-zero extension, multiplication by
`g.element` on a module need not have the expected kernel.  This file records the necessary
exactness hypothesis explicitly, proves it abstractly for flat modules, and exposes the canonical
quotient-to-range equivalence and division operation under that hypothesis.
-/

@[expose] public section

noncomputable section

universe u v w

namespace RingHom.SquareZeroExtension

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
variable {f : R' →+* R} [f.IsSquareZeroExtension]

/-- A module modulo the multiples of the intrinsic annihilator of the square-zero kernel. -/
@[stacks 09PS "module modulo the source kernel annihilator"]
abbrev sourceKernelQuotientModule (f : R' →+* R) [f.IsSquareZeroExtension]
    (M : Type w) [AddCommGroup M] [Module R' M] :=
  M ⧸ (sourceKernelAnnihilator f • (⊤ : Submodule R' M))

namespace Generator

variable (g : Generator f) (M : Type w) [AddCommGroup M] [Module R' M]

/-- Multiplication by the chosen kernel generator on an `R'`-module. -/
@[stacks 09PS "multiplication by a square-zero kernel generator on a module"]
def moduleMul : M →ₗ[R'] M :=
  LinearMap.lsmul R' M g.element

/-- Multiplication by the chosen generator acts by scalar multiplication. -/
@[simp]
theorem moduleMul_apply (x : M) :
    g.moduleMul M x = g.element • x := sorry

/-- The exactness condition needed to divide by the chosen generator on `M`: the kernel of
multiplication by the generator consists exactly of the multiples of its annihilator. -/
@[stacks 09PS "module exactness for a principal square-zero extension"]
def IsExactOn : Prop :=
  LinearMap.ker (g.moduleMul M) =
    sourceKernelAnnihilator f • (⊤ : Submodule R' M)

/-- The regular source module satisfies the generator exactness condition. -/
theorem isExactOn_source : g.IsExactOn R' := sorry

/-- Flat modules satisfy the generator exactness condition. -/
@[stacks 09PS "flat-module exactness for a principal square-zero extension"]
theorem isExactOn_of_flat [Module.Flat R' M] : g.IsExactOn M := sorry

/-- Under generator exactness, quotienting by the annihilator multiples identifies canonically
with the range of multiplication by the generator. -/
@[stacks 09PS "divide by a square-zero kernel generator"]
def quotientEquivRange (h : g.IsExactOn M) :
    sourceKernelQuotientModule f M ≃ₗ[R'] LinearMap.range (g.moduleMul M) :=
  (Submodule.quotEquivOfEq
      (sourceKernelAnnihilator f • (⊤ : Submodule R' M))
      (LinearMap.ker (g.moduleMul M)) h.symm).trans
    (g.moduleMul M).quotKerEquivRange

/-- The quotient-to-range equivalence sends a representative to its multiple by the chosen
generator. -/
@[simp]
theorem quotientEquivRange_apply_mk (h : g.IsExactOn M) (x : M) :
    ((g.quotientEquivRange M h (Submodule.Quotient.mk x) :
        LinearMap.range (g.moduleMul M)) : M) = g.element • x := sorry

section Divide

variable {N : Type*} [AddCommGroup N] [Module R' N]

/-- Divide a linear map whose values lie in the generator multiples by the chosen generator,
with values in the annihilator quotient. -/
@[stacks 09PS "linear division by a square-zero kernel generator"]
def divide (h : g.IsExactOn M) (u : N →ₗ[R'] M)
    (hu : ∀ x, u x ∈ LinearMap.range (g.moduleMul M)) :
    N →ₗ[R'] sourceKernelQuotientModule f M :=
  (g.quotientEquivRange M h).symm.toLinearMap.comp <|
    LinearMap.codRestrict (LinearMap.range (g.moduleMul M)) u hu

/-- Multiplying the divided value by the chosen generator recovers the original map. -/
@[simp]
theorem quotientEquivRange_divide (h : g.IsExactOn M) (u : N →ₗ[R'] M)
    (hu : ∀ x, u x ∈ LinearMap.range (g.moduleMul M)) (x : N) :
    (((g.quotientEquivRange M h) (g.divide M h u hu x) :
        LinearMap.range (g.moduleMul M)) : M) = u x := sorry

/-- Division by the generator is the unique quotient-valued linear map whose image under the
quotient-to-range equivalence is the prescribed map. -/
theorem eq_divide (h : g.IsExactOn M) (u : N →ₗ[R'] M)
    (hu : ∀ x, u x ∈ LinearMap.range (g.moduleMul M))
    (v : N →ₗ[R'] sourceKernelQuotientModule f M)
    (hv : ∀ x, (((g.quotientEquivRange M h) (v x) :
      LinearMap.range (g.moduleMul M)) : M) = u x) :
    v = g.divide M h u hu := sorry

end Divide

end Generator

end RingHom.SquareZeroExtension
