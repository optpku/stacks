/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth.RegularSequence

@[expose] public section

/-!
# Regular Sequences in Cohen--Macaulay Local Rings

The expected-codimension criterion below is independent of presentations and
belongs with the local Cohen--Macaulay self-module condition.

@stack 02JN
-/

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-- Lemma 10.104.2 (Stacks tag `02JN`): a list in the maximal ideal of a Noetherian
Cohen--Macaulay local ring is regular exactly when its quotient has the expected dimension. -/
@[stacks 02JN "Cohen-Macaulay regular-sequence dimension criterion"]
theorem isRegular_iff_ringKrullDim_quotient_add_length_eq {xs : List R}
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    RingTheory.Sequence.IsRegular R xs ↔
      ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R := sorry

/-- Lemma 10.104.2 (Stacks tag `02JN`): a regular prefix in the maximal
ideal of a Cohen--Macaulay local ring extends to a sequence of length
`ringKrullDim R`.
-/
@[stacks 02JN "maximal regular-sequence extension"]
theorem exists_maximal_regular_extension_of_ringKrullDim_quotient_add_length_eq
    {xs : List R} (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (hquot : ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R) :
    ∃ xs' : List R,
      RingTheory.Sequence.IsRegular R (xs ++ xs') ∧
        ringKrullDim R = (xs ++ xs').length := sorry

end Module.CohenMacaulay

namespace RingTheory.Sequence.IsRegular

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-- A regular sequence in a Cohen--Macaulay local ring extends to one whose
length is the Krull dimension of the ring. -/
@[stacks 02JN "maximal regular-sequence extension from regularity"]
theorem exists_extension_of_cohenMacaulay
    {xs : List R} (hreg : IsRegular R xs) :
    ∃ xs' : List R,
      IsRegular R (xs ++ xs') ∧ ringKrullDim R = (xs ++ xs').length := by
  have hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    exact hreg.ofList_le_maximalIdeal (Ideal.subset_span hx)
  exact Module.CohenMacaulay.exists_maximal_regular_extension_of_ringKrullDim_quotient_add_length_eq
    hxs ((Module.CohenMacaulay.isRegular_iff_ringKrullDim_quotient_add_length_eq hxs).mp hreg)

/-- A regular sequence in a Cohen--Macaulay local ring has Cohen--Macaulay
prefix quotients.  The quotient local-ring instance is explicit because the
result type depends on it. -/
@[stacks 02JN "Cohen-Macaulay prefix quotients"]
theorem cohenMacaulay_quotient_take
    {xs : List R} (hreg : IsRegular R xs) (i : ℕ)
    [IsLocalRing (R ⧸ Ideal.ofList (xs.take i))] :
    Module.CohenMacaulay (R ⧸ Ideal.ofList (xs.take i))
      (R ⧸ Ideal.ofList (xs.take i)) := sorry

end RingTheory.Sequence.IsRegular

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A regular sequence whose length is the Krull dimension makes a Noetherian local ring
Cohen--Macaulay. -/
theorem of_isRegular_of_length_eq_ringKrullDim {xs : List R}
    (hreg : RingTheory.Sequence.IsRegular R xs)
    (hlen : xs.length = ringKrullDim R) :
    Module.CohenMacaulay R R := sorry

/-- A finite module over a Noetherian local ring is Cohen--Macaulay when a regular
sequence has the dimension of its support. -/
theorem of_isRegular_of_supportDim_eq_length
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {xs : List R}
    (hreg : RingTheory.Sequence.IsRegular M xs)
    (hlen : Module.supportDim R M = xs.length) :
    Module.CohenMacaulay R M := sorry

end Module.CohenMacaulay
