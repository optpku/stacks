/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.31.8

@stack 045I
-/

/- Lemma 10.31.8: base change of a Noetherian algebra by a finitely generated
field extension is Noetherian. -/
@[stacks 045I]
#check @Algebra.EssFiniteType.isNoetherianRing_tensor_of_fieldExtension
