/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.AssociatedPrime
public import ReasLib.RingTheory.Depth.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal Quotients of Cohen--Macaulay Modules

This leaf owns the local one-step criterion for a principal quotient of a
Cohen--Macaulay module.  It separates the membership, regularity,
Cohen--Macaulayness, and depth conclusions so applications can use precisely
the part they need.
-/

@[expose] public section

open IsLocalRing
open scoped ENat Pointwise

universe u v

namespace Module.CohenMacaulay.QuotSMulTop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- In a Cohen--Macaulay local module, a one-step support-dimension drop forces the
quotient parameter into the maximal ideal. -/
@[stacks 00N5 "Cohen-Macaulay principal quotient parameter"]
theorem mem_maximalIdeal_of_dim_drop [Module.CohenMacaulay R M] {x : R}
    (hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M) :
    x ∈ maximalIdeal R := sorry

/-- In a Cohen--Macaulay local module, a one-step support-dimension drop makes the
quotient parameter regular. -/
@[stacks 00N5 "Cohen-Macaulay principal quotient regularity"]
theorem isSMulRegular_of_dim_drop [Module.CohenMacaulay R M] {x : R}
    (hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M) :
    IsSMulRegular M x := sorry

/-- The principal quotient at a one-step support-dimension drop of a Cohen--Macaulay local
module is Cohen--Macaulay. -/
@[stacks 00N5 "Cohen-Macaulay principal quotient"]
theorem cohenMacaulay_of_dim_drop [Module.CohenMacaulay R M] {x : R}
    (hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M) :
    Module.CohenMacaulay R (QuotSMulTop x M) := sorry

/-- At a one-step support-dimension drop, the principal quotient lowers local module depth by
one. -/
@[stacks 00N5 "depth of a Cohen-Macaulay principal quotient"]
theorem moduleDepth_eq_sub_one_of_dim_drop [Module.CohenMacaulay R M] {x : R}
    (hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M) :
    moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 := sorry

/-- A regular element in the maximal ideal preserves Cohen--Macaulayness across its principal
module quotient. -/
@[stacks 0C6G "Cohen-Macaulayness across a principal quotient"]
theorem iff_cohenMacaulay_of_mem_maximalIdeal [Module.Finite R M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    Module.CohenMacaulay R M ↔ Module.CohenMacaulay R (QuotSMulTop x M) := sorry

end Module.CohenMacaulay.QuotSMulTop
