/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Operations
import StacksCheckRecall

/-!
# Lemma 15.105.10

@stack 092K

The source gives faithfully-flat descent for tensor-square flatness and for weakly etale maps.
-/

@[expose] public section

/- Lemma 15.105.10 (1): tensor-square multiplication flatness descends along a faithfully flat
map. -/
@[stacks 092K "Lemma 15.105.10 (1)"]
#check @Algebra.TensorSquare.flat_of_faithfullyFlat

/- Lemma 15.105.10 (2): weakly-etale structure descends along a faithfully flat map. -/
@[stacks 092K "Lemma 15.105.10 (2)"]
#check @Algebra.WeaklyEtale.of_faithfullyFlat
