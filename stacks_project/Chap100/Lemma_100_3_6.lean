/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Lemma_100_3_6_Pullback
public import stacks_project.Chap100.Lemma_100_3_6_Comparison
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

/- Lemma 100.3.6: let `g : X' ⟶ X` be a morphism of algebraic stacks representable by
algebraic spaces, and let `[U / R] ⟶ X` be a presentation. Set `U' = U ×_X X'` and
`R' = R ×_X X'`. Then `(U', R', s', t', c')` is a groupoid in algebraic spaces,
`[U' / R'] ⟶ X'` is a presentation, and the square with left leg `[pr]` induced by the
groupoid morphism `pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)` is `2`-commutative. -/
@[stacks 04Y6] #check
  (Presentation.pullbackSquareIso :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (P : Presentation X) (g : X' ⟶ X)
      (hg : relativelyRepresentableByAlgebraicSpaces g),
      P.pullbackQuotientMap g hg ≫ P.hom ≅ (P.pullback g hg).hom ≫ g)
