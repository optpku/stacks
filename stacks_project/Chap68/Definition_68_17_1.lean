/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable
import StacksCheckRecall

@[expose] public section

/- Definition 68.17.1 (1): Let `S` be a scheme. An algebraic space `X` over `S`
has property `(β)` if `X` has the corresponding property of Lemma 68.5.1,
i.e. Lemma 68.4.3 holds at every point of `|X|`. -/
@[stacks 03KZ] #check AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta

/- Definition 68.17.1 (2): Let `f : X ⟶ Y` be a morphism of algebraic spaces
over a scheme `S`. We say `f` has property `(β)` if for any scheme `T` and
morphism `T ⟶ Y` the fibre product `T ×_Y X` has property `(β)`. -/
@[stacks 03KZ] #check AlgebraicGeometry.AlgebraicSpace.PropertyBeta

/- Definition 68.17.1 (3): Let `f : X ⟶ Y` be a morphism of algebraic spaces
over a scheme `S`. We say `f` is decent if for any scheme `T` and morphism
`T ⟶ Y` the fibre product `T ×_Y X` is a decent algebraic space. -/
@[stacks 03KZ] #check AlgebraicGeometry.AlgebraicSpace.Decent

/- Definition 68.17.1 (4): Let `f : X ⟶ Y` be a morphism of algebraic spaces
over a scheme `S`. We say `f` is reasonable if for any scheme `T` and morphism
`T ⟶ Y` the fibre product `T ×_Y X` is a reasonable algebraic space. -/
@[stacks 03KZ] #check AlgebraicGeometry.AlgebraicSpace.Reasonable

/- Definition 68.17.1 (5): Let `f : X ⟶ Y` be a morphism of algebraic spaces
over a scheme `S`. We say `f` is very reasonable if for any scheme `T` and
morphism `T ⟶ Y` the fibre product `T ×_Y X` is a very reasonable algebraic space. -/
@[stacks 03KZ] #check AlgebraicGeometry.AlgebraicSpace.VeryReasonable
