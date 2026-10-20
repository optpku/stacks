module

public import ReasLib.RingTheory.Extension.SquareZero

@[expose] public section

universe u

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

#check (Algebra.Exal A B N : Type u)
