/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Fppf
import StacksCheckRecall

/-!
# When a morphism of algebraic stacks is a gerbe

A morphism of algebraic stacks makes the source a gerbe over the target if and
only if both the morphism and its relative 2-diagonal are surjective, flat, and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Proposition 101.28.11: let `f : X ⟶ Y` be a morphism of algebraic stacks.
Then `X` is a gerbe over `Y` if and only if `f` and the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` are surjective, flat, and locally of finite
presentation. -/
@[stacks 0CPS] #check
  (AlgebraicGeometry.AlgebraicStack.gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Gerbe f ↔
      Surjective f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
          Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
            LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f))

/- A morphism of algebraic stacks that is surjective, flat, and locally of
finite presentation, and whose relative 2-diagonal is likewise surjective,
flat, and locally of finite presentation, is a gerbe over its target. -/
#check
  (AlgebraicGeometry.AlgebraicStack.instGerbe_of_surjective_flat_locallyOfFinitePresentation_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [Surjective (Hom.diagonal.{u + 1, u, u + 1} f)]
    [Flat (Hom.diagonal.{u + 1, u, u + 1} f)]
    [LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f)],
    Gerbe f)

end AlgebraicGeometry.AlgebraicStack
