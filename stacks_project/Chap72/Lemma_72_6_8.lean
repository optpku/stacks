module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
import StacksCheckRecall

/-!
# Additivity of principal Weil divisors

On a locally Noetherian integral algebraic space, the principal Weil divisor of
a product of rational units is the sum of the principal Weil divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- 0ENQ::statement_repair::1
Lemma 72.6.8: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f, g ∈ (RationalFunction X)ˣ`. Then
`principalWeilDivisor X (f * g) =
principalWeilDivisor X f + principalWeilDivisor X g`
as Weil divisors on `X`. -/
@[stacks 0ENQ]
#check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor_mul X :
  ∀ (f g : (RationalFunction X)ˣ),
    principalWeilDivisor X (f * g) =
      principalWeilDivisor X f + principalWeilDivisor X g)

end AlgebraicGeometry.AlgebraicSpace
