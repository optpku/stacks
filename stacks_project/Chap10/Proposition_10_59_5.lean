/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
import StacksCheckRecall

/-!
# Proposition 10.59.5

@stack 00K8
-/

@[expose] public section

/- Proposition 10.59.5 (1): if `R` is a Noetherian local ring, `M` is a
finite `R`-module, and `I` is an ideal of definition, then the
Hilbert--Samuel `φ`-function, extended to `ℤ` through `Int.toNat`, is a
numerical polynomial. -/
@[stacks 00K8]
#check @Ideal.HilbertSamuel.phi_isNumericalPolynomial_of_isIdealOfDefinition

/- Proposition 10.59.5 (2): under the same hypotheses, the Hilbert--Samuel
`χ`-function, extended to `ℤ` through `Int.toNat`, is a numerical
polynomial. -/
@[stacks 00K8]
#check @Ideal.HilbertSamuel.chi_isNumericalPolynomial_of_isIdealOfDefinition
