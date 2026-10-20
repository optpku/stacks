module

public import ReasLib.RingTheory.Henselian.Henselization.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Quotients of Henselizations

@stack 05WQ

The reusable quotient compatibility of a chosen henselization is owned by
`ReasLib.RingTheory.Henselian.Henselization.Quotient`.
-/

/- Chap10 Lemma 10 156 2, tag 05WQ: quotienting a henselization by the image
of a proper base ideal yields a henselization of the base quotient. -/
@[stacks 05WQ]
#check @IsHenselizationOf.quotient
