module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ring Equivalences of Separably Closed Fields

This leaf records the intrinsic invariance of separable closedness under ring
equivalence.  It is independent of any local-ring or henselization construction.
-/

universe u v

namespace IsSepClosed

/-- A ring equivalence transports separable closedness to its target field. -/
@[stacks 04GK "separably closed fields under ring equivalence"]
theorem of_ringEquiv {K : Type u} {L : Type v} [Field K] [Field L]
    [IsSepClosed K] (e : K ≃+* L) : IsSepClosed L := sorry

/-- Separable closedness is invariant under a ring equivalence of fields. -/
@[stacks 04GK "separably closedness and ring equivalence"]
theorem iff_of_ringEquiv {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) : IsSepClosed K ↔ IsSepClosed L := sorry

end IsSepClosed
