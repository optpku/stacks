/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.RegularSequence

@[expose] public section

/-!
# Good elements for Cohen--Macaulay modules

@stack 00N4

The predicate records the support dimensions of all prefix quotients.  Its
three consequences are kept separate so downstream code can consume only the
regularity, quotient, or shortened-sequence conclusion it needs.
-/

open scoped ENat Pointwise

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- An element is good with respect to `M` and `fs` when it lies in the
maximal ideal and gives the prescribed support dimension on every prefix
quotient. -/
@[stacks 00N4 "good element predicate"]
def IsGoodWithRespectTo
    (M : Type v) [AddCommGroup M] [Module R M] (g : R) (fs : List R) : Prop :=
  g ∈ IsLocalRing.maximalIdeal R ∧
    0 < fs.length ∧
      ∀ i : Fin fs.length,
        Module.supportDim R
            (QuotSMulTop g
              (M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule R M)))) =
          ((fs.length - i - 1 : ℕ) : WithBot ℕ∞)

namespace IsGoodWithRespectTo

variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.CohenMacaulay R M] {g : R} {fs : List R}

/-- Lemma 10.103.2 (1), tag 00N4: a good element for a maximal regular
sequence is regular on the Cohen--Macaulay module. -/
@[stacks 00N4 "(1), regularity"]
theorem isSMulRegular
    (hfs : RingTheory.Sequence.IsRegular M fs)
    (hMdim : Module.supportDim R M = fs.length)
    (hgood : IsGoodWithRespectTo M g fs) :
    IsSMulRegular M g := sorry

/-- Lemma 10.103.2 (2), tag 00N4: quotienting by a good element preserves
Cohen--Macaulayness. -/
@[stacks 00N4 "(2), quotient Cohen--Macaulayness"]
theorem cohenMacaulay_quotSMulTop
    (hfs : RingTheory.Sequence.IsRegular M fs)
    (hMdim : Module.supportDim R M = fs.length)
    (hgood : IsGoodWithRespectTo M g fs) :
    Module.CohenMacaulay R (QuotSMulTop g M) := sorry

/-- Lemma 10.103.2 (3), tag 00N4: after quotienting by a good element, the
shortened sequence is regular and realizes the quotient support dimension. -/
@[stacks 00N4 "(3), shortened regular sequence"]
theorem isRegular_take_and_supportDim_quotSMulTop_eq
    (hfs : RingTheory.Sequence.IsRegular M fs)
    (hMdim : Module.supportDim R M = fs.length)
    (hgood : IsGoodWithRespectTo M g fs) :
    RingTheory.Sequence.IsRegular (QuotSMulTop g M) (fs.take (fs.length - 1)) ∧
      Module.supportDim R (QuotSMulTop g M) = (fs.take (fs.length - 1)).length := sorry

end IsGoodWithRespectTo

end Module
