module

public import ReasLib.RingTheory.Sequence.Koszul.Family
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.28.2

@stack 0623
-/

/-!
# The Koszul complex of a finite family

The finite-family view and `KoszulComplex` notation are supplied by the neutral support library.
-/

/- Definition 15.28.2: a finite family is represented by the canonical linear form
`koszulLinearForm`, and `K•(f)` is its Koszul complex. -/
@[stacks 0623 "Koszul complex of a finite family"]
#check koszulLinearForm

#check @KoszulComplex.family
#check @KoszulComplex.powerComplex
