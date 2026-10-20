module

public import ReasLib.RingTheory.Regular.JRing.CompleteLocal
public import ReasLib.RingTheory.Regular.JRing.Dedekind
public import ReasLib.RingTheory.Regular.JRing.EssentialFiniteness
public import ReasLib.RingTheory.Regular.JRing.Field
import StacksCheckRecall

/-!
# Proposition 15.48.7

@stack 07PJ
-/

@[expose] public section

universe u

section

variable (K : Type u) [Field K]

/- Proposition 15.48.7 (1): fields are `J-2`. -/
@[stacks 07PJ "(1)"]
#check (inferInstance : IsJ2Ring K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.48.7 (2): Noetherian complete local rings are `J-2`. -/
@[stacks 07PJ "(2)"]
#check (inferInstance : IsJ2Ring R)

end

/- Proposition 15.48.7 (3): the ring of integers `ℤ` is `J-2`. -/
@[stacks 07PJ "(3)"]
#check (inferInstance : IsJ2Ring ℤ)

/- Proposition 15.48.7 (4): Noetherian local rings of Krull dimension one are `J-2`. -/
@[stacks 07PJ "(4)"]
#check @IsJ2Ring.of_localRing_dimensionOne

/- Proposition 15.48.7 (5): Nagata rings of Krull dimension one are `J-2`. -/
@[stacks 07PJ "(5)"]
#check @IsJ2Ring.of_nagataRing_dimensionOne

/- Proposition 15.48.7 (6): Dedekind domains with characteristic-zero fraction field are
`J-2`. -/
@[stacks 07PJ "(6)"]
#check @IsJ2Ring.dedekindOfFractionRingCharZero

/- Proposition 15.48.7 (7): finite type algebras over `J-2` rings are `J-2`. -/
@[stacks 07PJ "(7)"]
#check @IsJ2Ring.of_finiteType
