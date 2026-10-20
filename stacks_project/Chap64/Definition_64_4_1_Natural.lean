module

public import ReasLib.Algebra.Ring.CommutatorQuotient

universe u

variable (R : Type u) [NonUnitalNonAssocRing R]

#check (Ring.CommutatorQuotient.mk : R →+ Ring.CommutatorQuotient R)
