module

public import ReasLib.RingTheory.Etale.PolynomialFactorization.Counterexample
import StacksCheckRecall

/-!
# Example 15.9.7

The explicit ideal, polynomial, and no-lift theorem are owned by the shared etale-factorization
counterexample leaf.

@stack 07M2
-/

@[expose] public section

/- Example 15.9.7: the counterexample ideal is `4ℤ`. -/
@[stacks 07M2 "Example 15.9.7, ideal"]
#check @Algebra.EtaleFactorization.ModFour.ideal

/- Example 15.9.7: the reduced factor is `2 * X^2 + 2 * X + 1`. -/
@[stacks 07M2 "Example 15.9.7, reduced factor"]
#check @Algebra.EtaleFactorization.ModFour.factor

/- The displayed factorization and the failed leading-coefficient hypothesis. -/
@[stacks 07M2 "Example 15.9.7, factorization"]
#check @Algebra.EtaleFactorization.ModFour.factor_sq
#check @Algebra.EtaleFactorization.ModFour.factor_isCoprime
#check @Algebra.EtaleFactorization.ModFour.factor_leadingCoeff_not_isUnit

/- Example 15.9.7: no etale lift preserves this quotient factorization. -/
@[stacks 07M2 "Example 15.9.7, no lift"]
#check @Algebra.EtaleFactorization.ModFour.no_etale_factorization_lift
