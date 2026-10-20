/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Fppf
import StacksCheckRecall

/-!
# Gerbes are surjective and smooth

A morphism of algebraic stacks that makes the source a gerbe over the target
is surjective and smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.33.8 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is `Surjective`. -/
@[stacks 0DN8] #check
  (AlgebraicGeometry.AlgebraicStack.Surjective.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      Surjective f)

/- Lemma 101.33.8 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is `Smooth`. -/
@[stacks 0DN8] #check
  (AlgebraicGeometry.AlgebraicStack.Smooth.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      Smooth f)
