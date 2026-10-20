module

public import ReasLib.RingTheory.Polynomial.Int.XyEqSeven
import StacksCheckRecall

@[expose] public section

/- Exercise 111.58.6 -/
@[stacks 0D5L] #check
  (MvPolynomial.XyEqSeven.instIsRegularRing :
    IsRegularRing MvPolynomial.XyEqSeven.CoordinateRing)
