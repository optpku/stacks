module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)

/- Definition 23.6.1 (Tag 09PG): a divided-power structure on a strictly
graded-commutative nonnegatively graded algebra is the reusable structure on its positive-even
part, with the degree, normalization, product, sum, odd-product, and composition laws recorded
separately. -/
@[stacks 09PG] #check (NonnegGradedAlgebra.DividedPowers A : Type v)

#check @NonnegGradedAlgebra
#check @DividedPowerGradedAlgebra
#check @DividedPowerGradedAlgebra.forget
#check @NonnegGradedAlgebra.DividedPowers.gamma_degree
#check @NonnegGradedAlgebra.DividedPowers.gammaPiece
#check @NonnegGradedAlgebra.DividedPowers.gamma_mul
#check @NonnegGradedAlgebra.DividedPowers.gamma_oddMul
#check @NonnegGradedAlgebra.DividedPowers.gamma_add
#check @NonnegGradedAlgebra.DividedPowers.gamma_comp_pos
