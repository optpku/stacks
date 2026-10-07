module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

/-!
# Quotients of Complete Local Rings

This leaf records permanence of Noetherian complete local rings under proper
quotients.  The theorem is owned by `IsCompleteLocalRing`, so consumers can
use it directly when constructing a quotient instance.

@stack 0325
-/

universe u

namespace IsAdicComplete

/-- Adic completeness descends to a quotient of a Noetherian ring, for the
image of the defining ideal. -/
@[stacks 0325]
theorem quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (J I : Ideal R) [IsAdicComplete J R] :
    IsAdicComplete (J.map (Ideal.Quotient.mk I)) (R ⧸ I) := sorry

end IsAdicComplete

namespace IsCompleteLocalRing

/-- Lemma 10.160.2 (1), tag `0325`: a proper quotient of a Noetherian complete
local ring is a complete local ring. -/
@[stacks 0325]
theorem quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := sorry

end IsCompleteLocalRing
