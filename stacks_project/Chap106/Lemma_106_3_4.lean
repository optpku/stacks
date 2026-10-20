/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap106.Lemma_106_3_4_Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open scoped Bicategory

universe u

/- Lemma 106.3.4 (1): if `j : Y ⟶ Y'` is a thickening of algebraic stacks and
`f' : X' ⟶ Y'` is a morphism of algebraic stacks, the chosen 2-fibre product
`X = TwoFibreProduct.apex j f'` yields a morphism of thickenings
`(X ⊂ X') ⟶ (Y ⊂ Y')`. -/
@[stacks 0BPR] #check Hom.pullback

/- Lemma 106.3.4 (2): if `j : Y ⟶ Y'` is a first-order thickening of algebraic
stacks, then `TwoFibreProduct.snd j f' : X ⟶ X'` is a first-order thickening. -/
@[stacks 0BPR] #check IsFirstOrderThickening.twoFibreProduct_snd
