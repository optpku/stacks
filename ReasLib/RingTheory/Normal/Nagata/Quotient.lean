module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Quotients of Nagata Rings

@stack 032R

This leaf records the common quotient and domain bridge operations for Nagata
rings.
-/

universe u

namespace NagataRing

/-- A quotient of a Nagata ring is Nagata. -/
@[stacks 032R "Nagata quotients"]
theorem quotient {R : Type u} [CommRing R] [NagataRing R]
    (I : Ideal R) : NagataRing (R ⧸ I) := sorry

/-- A Nagata domain is an `N-2` domain. -/
@[stacks 032R "Nagata domains are N-2"]
theorem isN2Ring {R : Type u} [CommRing R] [IsDomain R] [NagataRing R] :
    IsN2Ring R := sorry

end NagataRing
