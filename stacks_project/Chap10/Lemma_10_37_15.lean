module

public import ReasLib.RingTheory.Normal.Ring
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.37.15 (Tag 0CYA): finite products of normal rings are normal.

@stack 0CYA
-/

/- Lemma 10.37.15: a finite product of normal rings is normal. -/
@[stacks 0CYA]
#check @IsNormalRing.pi

@[stacks 0CYA "finite-product normality instance"]
#check @IsNormalRing.instPi
