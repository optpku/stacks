/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_6_2_Weil
public import stacks_project.Chap72.Lemma_72_6_6

/-!
# Principal Weil divisors on algebraic spaces

The principal Weil divisor of a rational unit on a locally Noetherian integral
algebraic space is the locally finite sum of orders of vanishing along prime
divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The principal Weil divisor associated to a unit of the ring of rational
functions. -/
def principalWeilDivisor (f : (RationalFunction X)ˣ) : WeilDivisor X :=
  WeilDivisor.ofCoeff X (fun Z ↦ Z.ord f)
    (locallyFinite_primeDivisors_ord_ne_zero X f)

/-- The coefficient of a principal Weil divisor at a prime divisor is the
corresponding order of vanishing. -/
theorem principalWeilDivisor_coeff (f : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    (principalWeilDivisor X f).coeff Z = Z.ord f :=
  sorry

/-- The principal Weil divisor of the unit `1` is zero. -/
theorem principalWeilDivisor_one : principalWeilDivisor X 1 = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

