/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.GeometricallyNormal.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.165.5

@stack 06DF
-/

/- Lemma 10.165.5 (Stacks tag `06DF`): the shared tensor-product owner gives
normality when the left factor is geometrically normal and the right factor is
normal. -/
@[stacks 06DF]
#check @Algebra.TensorProduct.isNormalRing_of_isGeometricallyNormal_left

@[stacks 06DF "normal right factor"]
#check @Algebra.TensorProduct.isNormalRing_of_isGeometricallyNormal_right
