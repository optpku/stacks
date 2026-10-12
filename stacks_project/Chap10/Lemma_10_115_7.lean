/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.FactorizationAway
import StacksCheckRecall

@[expose] public section

/-!
# Relative Noether Normalization Away From One Element

@stack 07NA

The intermediate subalgebra and finite injective polynomial map are explicit
data of `IsFactorizationAway`; `awayEquiv` derives the source's localization
isomorphism from its canonical-map bijectivity field.
-/

/- Lemma 10.115.7 [stacks 07NA]: an injective finite-type map from a domain
admits a finite injective polynomial factorization that becomes an isomorphism
after inverting one nonzero base element. -/
@[stacks 07NA "existence of a factorization away"]
#check @MvPolynomial.NoetherNormalization.exists_factorizationAway

@[stacks 07NA "factorization-away data"]
#check @MvPolynomial.NoetherNormalization.IsFactorizationAway

@[stacks 07NA "factorization-away specification"]
#check @MvPolynomial.NoetherNormalization.IsFactorizationAway.spec

@[stacks 07NA "localization equivalence"]
#check @MvPolynomial.NoetherNormalization.IsFactorizationAway.awayEquiv
