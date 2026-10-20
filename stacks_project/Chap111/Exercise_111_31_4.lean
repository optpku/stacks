module

public import ReasLib.AlgebraicGeometry.AffineSpace.PuncturedLine
import StacksCheckRecall

@[expose] public section

/- Exercise 111.31.4 (1): the complex x-axis is an affine cone. -/
@[stacks 0E9G] #check (MvPolynomial.LineCone.isCone_line :
  MvPolynomial.IsCone MvPolynomial.LineCone.line)

/- Exercise 111.31.4 (2): the reciprocal coordinate function on the punctured
complex x-axis is regular. -/
@[stacks 0E9G] #check (MvPolynomial.LineCone.isRegular_reciprocal :
  MvPolynomial.IsRegular MvPolynomial.LineCone.reciprocal)

/- Exercise 111.31.4 (3): the reciprocal coordinate function is not the restriction
of any polynomial on the ambient complex affine plane. -/
@[stacks 0E9G] #check (MvPolynomial.LineCone.not_isPolynomial_reciprocal :
  ¬ MvPolynomial.IsPolynomial MvPolynomial.LineCone.reciprocal)

#check (MvPolynomial.LineCone.lineIdeal_isPrime : MvPolynomial.LineCone.lineIdeal.IsPrime)

#check (MvPolynomial.LineCone.isZariskiOpenIn_punctured :
  MvPolynomial.IsZariskiOpenIn MvPolynomial.LineCone.punctured MvPolynomial.LineCone.line)
