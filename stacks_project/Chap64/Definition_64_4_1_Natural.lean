/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Ring.CommutatorQuotient

universe u

variable (R : Type u) [NonUnitalNonAssocRing R]

#check (Ring.CommutatorQuotient.mk : R →+ Ring.CommutatorQuotient R)
