/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

/-!
# Quotients of Henselian Local Rings

@stack 05WQ

This leaf owns the intrinsic henselianity of proper quotients.  It depends only
on the canonical local-ring quotient API, so downstream users need not import
a particular henselization construction.
-/

universe u

namespace HenselianLocalRing

/-- Tag `05WQ`: a proper quotient of a henselian local ring is henselian. -/
@[stacks 05WQ "henselian proper quotient"]
theorem quotient {R : Type u} [CommRing R] [HenselianLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) : HenselianLocalRing (R ⧸ I) := sorry

end HenselianLocalRing
