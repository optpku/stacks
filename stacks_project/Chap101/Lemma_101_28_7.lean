/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.LocalQuotient
import StacksCheckRecall

/-!
# Local classifying presentations of gerbes of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.28.7: a morphism of algebraic stacks is a gerbe precisely when
an fppf algebraic-space cover of its target makes it a trivial-action quotient
by a flat, locally finitely presented group algebraic space, over that cover. -/
@[stacks 06QH] #check
  (AlgebraicGeometry.AlgebraicStack.Gerbe.iff_exists_trivialQuotient :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (π : X ⟶ Y),
      AlgebraicGeometry.AlgebraicStack.Gerbe π ↔
        ∃ (U : AlgebraicSpace S) (G : GroupAlgebraicSpace U)
          (g : U.toGroupoids ⟶ Y),
          AlgebraicSpace.Flat G.X.hom ∧
            AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ∧
            AlgebraicGeometry.AlgebraicStack.Surjective g ∧
            AlgebraicGeometry.AlgebraicStack.Flat g ∧
            AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation g ∧
              AlgebraicGeometry.AlgebraicStack.IsTrivialActionQuotientOver
                (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π g) G)
