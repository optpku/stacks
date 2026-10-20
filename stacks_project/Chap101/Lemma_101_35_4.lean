/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.OpenImmersion
import StacksCheckRecall

/-!
# Open immersions of algebraic stacks are étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.35.4: An open immersion of algebraic stacks is étale. -/
@[stacks 0CIP]
#check (AlgebraicGeometry.AlgebraicStack.etale_of_openImmersion :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.OpenImmersion f],
    AlgebraicGeometry.AlgebraicStack.Etale f)
