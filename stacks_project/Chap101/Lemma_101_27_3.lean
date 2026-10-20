/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.BaseChange
import StacksCheckRecall

/-!
# Base change of finite presentation morphisms of algebraic stacks

A base change of a finitely presented morphism of algebraic stacks is of
finite presentation. The same holds for morphisms which are locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.27.3: A base change of a finitely presented morphism of algebraic
stacks is of finite presentation. The same holds for morphisms which are
locally of finite presentation. The base change of `f : X ⟶ Y` along
`g : Z ⟶ Y` is the canonical second projection of their 2-fibre product. -/
@[stacks 06Q4] #check
  (AlgebraicGeometry.AlgebraicStack.FinitePresentation.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S},
      [AlgebraicStack X] → [AlgebraicStack Y] → [AlgebraicStack Z] →
      (f : X ⟶ Y) → (g : Z ⟶ Y) → [AlgebraicStack.FinitePresentation f] →
      AlgebraicStack.FinitePresentation
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S},
      [AlgebraicStack X] → [AlgebraicStack Y] → [AlgebraicStack Z] →
      (f : X ⟶ Y) → (g : Z ⟶ Y) → [AlgebraicStack.LocallyOfFinitePresentation f] →
      AlgebraicStack.LocallyOfFinitePresentation
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
