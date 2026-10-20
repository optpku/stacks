module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Gluing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 67.47.3: for a scheme `S` and an algebraic space `X` over `S`, the ring `R(X)` of
rational functions on `X` is the commutative ring whose elements are rational maps from `X` to
the affine line `𝔸¹_S`, with addition and multiplication induced by the ring-object structure of
`𝔸¹_S`. -/
@[stacks 0EMP] #check
  (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRing :
    {S : Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → CommRingCat.{u + 1})

#check AlgebraicGeometry.AlgebraicSpace.RationalFunction
#check AlgebraicGeometry.AlgebraicSpace.affineLine
