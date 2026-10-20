module

public import ReasLib.RingTheory.FormalFiber.GRing.Henselization
import StacksCheckRecall

/-!
# Lemma 15.50.8

@stack 07QR
-/

@[expose] public section

/- Lemma 15.50.8 (1): a henselization of a Noetherian local G-ring is a G-ring. -/
@[stacks 07QR "(1)"]
#check @IsHenselizationOf.isGRing

/- Lemma 15.50.8 (2): a strict henselization of a Noetherian local G-ring is a G-ring. -/
@[stacks 07QR "(2)"]
#check @IsStrictHenselizationOf.isGRing
