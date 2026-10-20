module

public import ReasLib.RingTheory.Etale.Weakly.ResidueField
import StacksCheckRecall

@[expose] public section

/-!
# Residue fields along weakly etale maps

Lemma 15.105.17 is owned by the reusable weakly-etale residue-field API.

@stack 092R
-/

/- Lemma 15.105.17: a weakly etale ring map induces algebraic and separable
extensions between the residue fields of every lying-over pair of primes. -/
@[stacks 092R "Lemma 15.105.17 (1)"]
#check @Algebra.WeaklyEtale.residueField_isAlgebraic

@[stacks 092R "Lemma 15.105.17 (2)"]
#check @Algebra.WeaklyEtale.residueField_isSeparable

@[stacks 092R "induced algebra on a lying-over residue-field pair"]
#check @Ideal.ResidueField.algebraOfLiesOver
