/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Triangular
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.115.2

@stack 051N

The reusable owner is valid over commutative semirings. Its support witness
also implies the source's explicit nonvanishing condition on the leading
coefficient, so no `Fin`-specific chapter wrapper is needed.
-/

@[stacks 051N "triangular substitution with constant leading coefficient"]
#check @MvPolynomial.NoetherNormalization.exists_positive_natDegree_and_constant_leadingCoeff

#check @MvPolynomial.NoetherNormalization.DominatingWeights
#check @MvPolynomial.NoetherNormalization.addShear
#check @MvPolynomial.NoetherNormalization.lastVariablePolynomial
#check @MvPolynomial.Fin.lastVariableEquiv
