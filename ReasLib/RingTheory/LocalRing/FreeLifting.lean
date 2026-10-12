/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Freeness across a regular principal quotient

The general finite-presentation criterion is owned by Mathlib as
`Module.free_quotSMulTop_iff_free`.  This leaf keeps that canonical entry visible and adds only
the source-facing finite Noetherian local-ring specialization, so downstream files can import a
ReasLib module instead of a chapter file.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Module.Free.LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- The canonical reusable criterion; the local-ring theorem below is its source-facing bridge. -/

/-- Lemma 10.106.5 (Stacks `00NS`): over a Noetherian local ring, a finite module is free when a
regular element in the maximal ideal acts regularly and the principal quotient module is free. -/
@[stacks 00NS]
theorem of_regular_quotient
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := sorry

end Module.Free.LocalRing
