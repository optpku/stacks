/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.BaseChange
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
@[stacks 0BPR] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.pullback :
  ∀ {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening j],
    Hom (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f') j
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} j f') f')

/- Lemma 106.3.4 (2): if `j : Y ⟶ Y'` is a first-order thickening of algebraic
stacks, then `TwoFibreProduct.snd j f' : X ⟶ X'` is a first-order thickening. -/
@[stacks 0BPR] #check (AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {Y Y' X' : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack X']
    (j : Y ⟶ Y') (f' : X' ⟶ Y') [IsFirstOrderThickening j],
    IsFirstOrderThickening (TwoFibreProduct.snd.{u + 1, u, u + 1, u} j f'))

