/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Fppf
import StacksCheckRecall

/-!
# Gerbes are surjective, flat, and locally of finite presentation

A morphism of algebraic stacks that makes the source a gerbe over the target
is surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.28.8 (1): A gerbe morphism of algebraic stacks is surjective. -/
@[stacks 06QI] #check
  (AlgebraicGeometry.AlgebraicStack.Surjective.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      Surjective f)

/- Lemma 101.28.8 (2): A gerbe morphism of algebraic stacks is flat. -/
@[stacks 06QI] #check
  (AlgebraicGeometry.AlgebraicStack.Flat.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      Flat f)

/- Lemma 101.28.8 (3): A gerbe morphism of algebraic stacks is locally of finite
presentation. -/
@[stacks 06QI] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      LocallyOfFinitePresentation f)

end AlgebraicGeometry.AlgebraicStack
