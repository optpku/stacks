module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Quotients of Strict Henselizations

@stack 05WS

The reusable quotient compatibility of a chosen strict henselization is owned
by `ReasLib.RingTheory.Henselian.StrictHenselization.Quotient`.
-/

/- Chap10 Lemma 10 156 4, tag 05WS: quotienting a strict henselization by the image
of a proper base ideal yields a strict henselization of the base quotient. -/
@[stacks 05WS]
#check @IsStrictHenselizationOf.quotient
