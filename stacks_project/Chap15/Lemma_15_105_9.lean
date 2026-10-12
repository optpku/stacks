/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Operations
import StacksCheckRecall

/-!
# Lemma 15.105.9

@stack 092J

The source has two clauses: flatness of tensor-square multiplication in a tower, and stability of
weakly etale maps under composition.
-/

@[expose] public section

/- Lemma 15.105.9 (1): flat tensor-square multiplication maps compose in an algebra tower. -/
@[stacks 092J "Lemma 15.105.9 (1)"]
#check @Algebra.TensorSquare.flat_comp

/- Lemma 15.105.9 (2): weakly etale maps are stable under composition. -/
@[stacks 092J "Lemma 15.105.9 (2)"]
#check @Algebra.WeaklyEtale.comp
