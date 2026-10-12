/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Lemma_94_19_1_Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.19.2: let `Sch_fppf` be a big fppf site. Let `g : S ⟶ S'` be a
morphism of this site. If `p : X ⟶ (Sch/S)_fppf` is an algebraic stack over `S`,
then `X` viewed as an algebraic stack over `S'` is the algebraic stack
`X ⟶ (Sch/S')_fppf` given by `AlgebraicStack.viewedOver g X`, i.e. Construction A
of Lemma 94.19.1. Its structure morphism is `X.p ⋙ Over.map g`. -/
@[stacks 04X6] #check AlgebraicGeometry.AlgebraicStack.viewedOver
