/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_4_1_Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 70.4.2: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{ii'})` be an inverse system over `I` of algebraic spaces over `S`
with affine transition maps. Let `X = lim_i X_i`. Let `0 ∈ I`. Suppose that
`T ⟶ X_0` is a morphism of algebraic spaces. Then
`T ×_{X_0} X = lim_{i ≥ 0} T ×_{X_0} X_i` as algebraic spaces over `S`. -/
@[stacks 07SH] #check AlgebraicGeometry.AlgebraicSpace.DirectedAffine.pullback_π_iso
