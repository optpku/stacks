module

public import stacks_project.Chap72.Definition_72_6_9_Principal

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

/-- The order of vanishing of a product of rational units along a prime divisor is
the sum of the orders of vanishing. -/
theorem orderOfVanishing_mul (Z : PrimeDivisor X) (f g : (RationalFunction X)ˣ) :
    Z.ord (f * g) = Z.ord f + Z.ord g := sorry

/-- Coefficients of principal Weil divisors are additive in rational units. -/
theorem principalWeilDivisor_mul_coeff (f g : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    (principalWeilDivisor X (f * g)).coeff Z =
      (principalWeilDivisor X f).coeff Z + (principalWeilDivisor X g).coeff Z := sorry

/-- Lemma 72.6.8: Let `S` be a scheme. Let `X` be a locally Noetherian integral
algebraic space over `S`. Let `f, g ∈ (RationalFunction X)ˣ`. Then
`principalWeilDivisor X (f * g) =
principalWeilDivisor X f + principalWeilDivisor X g`
as Weil divisors on `X`. -/
@[stacks 0ENQ]
theorem principalWeilDivisor_mul (f g : (RationalFunction X)ˣ) :
    principalWeilDivisor X (f * g) =
      principalWeilDivisor X f + principalWeilDivisor X g := sorry

end AlgebraicGeometry.AlgebraicSpace
