/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.EmbeddingDimension

@[expose] public section

/-!
# Regular Local Rings and Regular Sequence Quotients

This leaf owns the converse regularity criterion: regular-locality of a
quotient by a regular sequence lifts to the ambient Noetherian local ring.
-/

universe u

namespace IsRegularLocalRing

/-- Lemma 10.106.7 (Tag 00NU): if `rs` is a regular sequence in a Noetherian
local ring `R` and `R ⧸ Ideal.ofList rs` is a regular local ring, then `R` is
a regular local ring. -/
@[stacks 00NU]
theorem of_quotient_of_isRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {rs : List R} (hreg : RingTheory.Sequence.IsRegular R rs)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.ofList rs)) :
    IsRegularLocalRing R := sorry

/-- Regular-locality lifts from a principal quotient by a regular element of
the maximal ideal. -/
@[stacks 00NU "regular principal quotient lifting"]
theorem of_quotient_span_singleton_of_isRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : IsLocalRing.maximalIdeal R) (hx : IsRegular (x : R))
    (hquot : IsRegularLocalRing (R ⧸ Ideal.span ({(x : R)} : Set R))) :
    IsRegularLocalRing R := sorry

/-- Killing an element outside the square of the maximal ideal of a regular
local ring again gives a regular local ring. -/
@[stacks 07DX "regular local cotangent-direction quotient"]
theorem quotient_span_singleton_of_not_mem_sq
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (x : IsLocalRing.maximalIdeal R)
    (hx : (x : R) ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({(x : R)} : Set R)) := sorry

end IsRegularLocalRing
