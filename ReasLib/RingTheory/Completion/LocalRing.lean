module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete Local Rings

A complete local ring is a local ring that is complete for the adic topology defined by its
maximal ideal.

## Main definitions

* `IsCompleteLocalRing` — class combining `IsLocalRing` and `IsAdicComplete` for the maximal ideal.
-/

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R]

/-- A complete local ring is a local ring that is complete for the adic topology defined by its
maximal ideal. -/
@[stacks 0324]
class IsCompleteLocalRing : Prop extends IsLocalRing R, IsAdicComplete (maximalIdeal R) R

/-- Unfold complete-local-ring structure into locality and completeness for the resulting
maximal-adic topology. -/
@[stacks 0324 "complete local ring specification"]
theorem isCompleteLocalRing_iff :
    IsCompleteLocalRing R ↔
      ∃ hlocal : IsLocalRing R,
        -- Local instance justification (defeq pin): Bind the existential locality witness so maximalIdeal R and its adic completeness use that witness without requiring an ambient IsLocalRing assumption. This is a dependent specification, not a convenience instance.
        letI := hlocal
        IsAdicComplete (maximalIdeal R) R := sorry

variable {R}

/-- Any local ring that is adically complete with respect to its maximal ideal is a complete local
ring. -/
instance [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] : IsCompleteLocalRing R := {}

end
