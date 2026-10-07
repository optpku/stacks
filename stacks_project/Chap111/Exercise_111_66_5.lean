module

public import ReasLib.AlgebraicGeometry.AffineQuintic
import StacksCheckRecall

open scoped AlgebraicGeometry

/- Exercise 111.66.5: the closed complex point `(1, 1)` is singular on
`Spec (ℂ[x, y] ⧸ (x ^ 5 - 5 * x * y ^ 4 + 20 * y - 16))`, viewed as a variety over `ℂ`. -/
@[stacks 0H8U] #check
  (AlgebraicGeometry.AffineQuintic.singularPoint_mem_singularLocus :
    AlgebraicGeometry.AffineQuintic.singularPoint ∈
      AlgebraicGeometry.Scheme.singularLocus AlgebraicGeometry.AffineQuintic.scheme)
