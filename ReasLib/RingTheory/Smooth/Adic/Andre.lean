/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.LocalRing.ResidueField.ClosedFiber
public import ReasLib.RingTheory.Regular.RingMap
public import ReasLib.RingTheory.Smooth.Adic.Completion
import Mathlib.Tactic.CrossRefAttribute

/-!
# André's criterion for regular local maps

This leaf records the equivalence between regularity, geometric regularity of the closed fiber,
and adic formal smoothness when the source-to-completion map is regular.

@stack 07PM
@stack 0H7U
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

-- Syntax shorthands for the two closed-fiber objects repeated in the four equivalent clauses.
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "mClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/-- Theorem 15.49.3 (André): assume that the completion map of the Noetherian local ring `A` is
regular.  For a local map `A → B`, regularity is equivalent to geometric regularity of the
closed fiber together with flatness, to formal smoothness of that fiber over `ResidueField A`,
and to formal smoothness of `A → B` for the maximal-ideal-adic topology. -/
@[stacks 0H7U]
theorem regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion
    (hA_completion :
      (algebraMap A (AdicCompletion (maximalIdeal A) A)).Regular) :
    List.TFAE [
      (algebraMap A B).Regular,
      (algebraMap A B).Flat ∧
        Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        (algebraMap (ResidueField A) ClosedFiber).formally_smooth_for_adic mClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end

section CompleteLocal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]

-- Repeat the syntax shorthands in this independent specialization section; they do not escape it.
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "mClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/-- Proposition 15.49.2: over a Noetherian complete local source, regularity of a local map is
equivalent to the closed-fiber and adic formal-smoothness criteria. -/
@[stacks 07PM "regular local map criteria over a complete local source"]
theorem regularRingMap_specialFiber_formallySmooth_tfae_of_completeLocal :
    List.TFAE [
      (algebraMap A B).Regular,
      (algebraMap A B).Flat ∧
        Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        (algebraMap (ResidueField A) ClosedFiber).formally_smooth_for_adic mClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end CompleteLocal
