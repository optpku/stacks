module

import StacksCheckRecall
public import ReasLib.RingTheory.Normal.Polynomial

@[expose] public section

/-!
# Normal Polynomial Rings

The reusable normal-polynomial API is owned by ReasLib; this chapter file
records the textbook entry point.

@stack 00H1
-/

-- Lemma 10.37.14, tag `00H1`: a polynomial ring over a normal ring is normal.
@[stacks 00H1 "polynomial rings over normal rings are normal"]
#check @IsNormalRing.polynomial

@[stacks 00H1 "polynomial normality instance"]
#check @Polynomial.instIsNormalRing
