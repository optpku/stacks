module

public import ReasLib.RingTheory.Regular.GRing.CompleteLocal
public import ReasLib.RingTheory.Regular.GRing.Dedekind
public import ReasLib.RingTheory.Regular.GRing.EssentialFiniteness
public import ReasLib.RingTheory.Regular.GRing.Field
import StacksCheckRecall

/-!
# Proposition 15.50.12

@stack 07PX
-/

@[expose] public section

universe u

section

variable (K : Type u) [Field K]

/- Proposition 15.50.12 (1): fields are `G`-rings. -/
@[stacks 07PX "(1)"]
#check (inferInstance : IsGRing K)

end


section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.50.12 (2): Noetherian complete local rings are `G`-rings. -/
@[stacks 07PX "(2)"]
#check (inferInstance : IsGRing R)

end


/- Proposition 15.50.12 (3): the ring of integers `ℤ` is a `G`-ring. -/
@[stacks 07PX "(3)"]
#check (inferInstance : IsGRing ℤ)

/- Proposition 15.50.12 (4): characteristic-zero Dedekind domains are `G`-rings. -/
@[stacks 07PX "(4)"]
#check @IsGRing.dedekindOfFractionRingCharZero

/- Proposition 15.50.12 (5): finite type extensions of `G`-rings are `G`-rings. -/
@[stacks 07PX "(5)"]
#check @IsGRing.of_finiteType
