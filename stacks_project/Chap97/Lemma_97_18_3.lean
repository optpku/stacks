/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Algebraic
import StacksCheckRecall

/-!
# When the classifying quotient stack is algebraic

The quotient stack of the trivial action of a group algebraic space `G` over an
algebraic space `B` over a scheme `S` is algebraic if and only if `G ⟶ B` is
flat and locally of finite presentation.
-/

universe u

/- Lemma 97.18.3. Let `S` be a scheme and let `B` be an algebraic space over
`S`. Let `G` be a group algebraic space over `B`. Endow `B` with the trivial
action of `G`. Then the quotient stack of `B` by `G` is an algebraic stack if
and only if `G` is flat and locally of finite presentation over `B`. -/
@[stacks 06PL] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isAlgebraicStack_trivialAction_iff :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B),
      AlgebraicGeometry.AlgebraicStack
        (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.quotientStack
          (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction G
            (AlgebraicGeometry.GroupAlgebraicSpace.trivialAction G))) ↔
        AlgebraicGeometry.AlgebraicSpace.Flat G.X.hom ∧
          AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation G.X.hom)
