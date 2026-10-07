module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.RingTheory.Ideal.OfList
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ideal bounds for regular sequences

This leaf contains the small bridge between the canonical regular-sequence
predicate and the source-facing phrase “regular in an ideal”.  The predicate
itself remains `RingTheory.Sequence.IsRegular`; this file only exposes the
ideal-membership view needed by downstream arguments.
-/

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A regular sequence lies in an ideal exactly when its generated ideal is
contained in that ideal. -/
@[stacks 00LF "regular sequence contained in an ideal"]
theorem isRegular_in_ideal_iff (I : Ideal R) (rs : List R) :
    (IsRegular M rs ∧ Ideal.ofList rs ≤ I) ↔
      IsRegular M rs ∧ ∀ r ∈ rs, r ∈ I := sorry
/- Proof strategy: rewrite the second conjunct with
`Ideal.ofList_le_iff`, then use `and_congr` (or `rw`). -/

end RingTheory.Sequence
