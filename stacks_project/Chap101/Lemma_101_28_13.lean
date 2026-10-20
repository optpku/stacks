/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.UniversalHomeomorphism
import StacksCheckRecall

/-!
# Gerbes are universal homeomorphisms

A morphism of algebraic stacks that makes the source a gerbe over the target
is a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.28.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is a universal homeomorphism. -/
@[stacks 06R9] #check
  (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      UniversalHomeomorphism f)

/- A gerbe morphism of algebraic stacks induces a homeomorphism on underlying
point spaces. -/
#check
  (AlgebraicGeometry.AlgebraicStack.pointsIsHomeomorph_of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      pointsIsHomeomorph f)

end AlgebraicGeometry.AlgebraicStack
