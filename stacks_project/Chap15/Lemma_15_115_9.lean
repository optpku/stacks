/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Ramification
import StacksCheckRecall

/-!
# Lemma 15.115.9

@stack 0EXY

The raw tensor product is canonically equivalent to its reduction, so its finite field factors
and their ramification properties are owned without choosing a product decomposition.
-/

@[expose] public section

/- Lemma 15.115.9 (setup): the separable raw tensor product is its canonical reduction. -/
@[stacks 0EXY "finite separable raw tensor product"]
#check @FieldExtension.TensorProduct.tensorEquivReduced

/- Lemma 15.115.9 (setup): the reduced tensor product is a finite product of fields. -/
@[stacks 0EXY "finite product of tensor branches"]
#check @FieldExtension.TensorProduct.reduced_finiteProductOfFields

/- Lemma 15.115.9 (1): unramified source extensions have unramified raw tensor branches. -/
@[stacks 0EXY "unramified raw tensor branches"]
#check @DVR.Field.BaseChange.IsUnramified.rawBranch

/- Lemma 15.115.9 (2): tamely ramified source extensions have tamely ramified raw tensor
branches. -/
@[stacks 0EXY "tamely ramified raw tensor branches"]
#check @DVR.Field.BaseChange.IsTamelyRamified.rawBranch
