/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Excellent.CompleteLocal
public import ReasLib.RingTheory.Excellent.Dedekind
public import ReasLib.RingTheory.Excellent.EssentialFiniteness
public import ReasLib.RingTheory.Excellent.Field
import StacksCheckRecall

/-!
# Proposition 15.52.3

@stack 07QW
-/

@[expose] public section

universe u

section


variable (K : Type u) [Field K]

/- Proposition 15.52.3 (1): fields are excellent. -/
@[stacks 07QW "(1)"]
#check (inferInstance : IsExcellentRing K)

end


section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.52.3 (2): Noetherian complete local rings are excellent. -/
@[stacks 07QW "(2)"]
#check (inferInstance : IsExcellentRing R)

end


/- Proposition 15.52.3 (3): the ring of integers `ℤ` is excellent. -/
@[stacks 07QW "(3)"]
#check (inferInstance : IsExcellentRing ℤ)

/- Proposition 15.52.3 (4): characteristic-zero Dedekind domains are excellent. -/
@[stacks 07QW "(4)"]
#check @IsExcellentRing.dedekindOfFractionRingCharZero

/- Proposition 15.52.3 (5): finite type extensions of excellent rings are excellent. -/
@[stacks 07QW "(5)"]
#check @IsExcellentRing.of_finiteType
