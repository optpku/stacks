/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Lemma_94_14_2_Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 94.14.2: let `S` be a scheme contained in `Sch_fppf`. Let `Z` be a
stack in groupoids over `(Sch/S)_fppf` whose diagonal is representable by
algebraic spaces. Let `X`, `Y` be algebraic stacks over `S`. Let `f : X ⟶ Z`,
`g : Y ⟶ Z` be 1-morphisms of stacks in groupoids. Then the 2-fibre product
`X ×_{f, Z, g} Y` is an algebraic stack. -/
@[stacks 04TF]
#check AlgebraicGeometry.AlgebraicStack.twoFibreProduct
