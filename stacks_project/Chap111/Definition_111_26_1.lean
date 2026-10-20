module

public import ReasLib.RingTheory.Polynomial.IntegerValued
import StacksCheckRecall

@[expose] public section

/- Definition 111.26.1: a numerical polynomial is a polynomial `f` in `Polynomial ℚ`
such that `f.eval (algebraMap ℤ ℚ n)` lies in `Set.range (algebraMap ℤ ℚ)` for every
integer `n`. This is the owner `Polynomial.IsIntegerValued`. -/
@[stacks 027X]
#check (Polynomial.IsIntegerValued : Polynomial ℚ → Prop)
