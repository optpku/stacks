module

import StacksCheckRecall
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

universe u

section

variable (A : Type u) [CommRing A] [IsRationalSingularity A]
variable [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
variable [IsGorensteinLocalRing A]
variable (h_notRegular : ¬ IsRegularLocalRing A)

/- Situation 54.12.1 (1): `A` is a two-dimensional Nagata normal local domain defining a
rational singularity. -/
@[stacks 0BGC] #check (IsRationalSingularity A : Prop)

/- The completion of `A` at its maximal ideal is normal. -/
#check
  (inferInstance : IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A))

/- `A` is Gorenstein. -/
#check (inferInstance : IsGorensteinLocalRing A)

/- `A` is not regular. -/
#check (h_notRegular : ¬ IsRegularLocalRing A)

end
