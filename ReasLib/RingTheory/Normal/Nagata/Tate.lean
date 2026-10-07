module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Tate's Criterion for Japanese Domains

This module records the principal-adic lifting criterion for the `N-2`
condition on a normal Noetherian domain.
-/

universe u

namespace IsN2Ring

variable {R : Type u}

/-- Lemma 10.161.16 (Tate), tag `032P`: a normal Noetherian domain is `N-2` if it is complete
for the topology defined by a principal ideal whose quotient is an `N-2` domain. -/
@[stacks 032P]
theorem of_principalAdicComplete
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (x : R) [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    [IsN2Ring (R ⧸ Ideal.span ({x} : Set R))]
    [IsAdicComplete (Ideal.span ({x} : Set R)) R] :
    IsN2Ring R := sorry

end IsN2Ring
