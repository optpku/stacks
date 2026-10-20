/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiberDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Definition 107.5.2: if `f : T.toGroupoids ⟶ X` is a locally of finite type
morphism from an algebraic space to an algebraic stack, and `t ∈ |T|` is a
point with image `x ∈ |X|`, the relative dimension `dim_t(T_x)` is
`fiberDimensionAt f t`. Choose a morphism `Spec k ⟶ X` representing `x` and
a point `t'` of `T ×_X Spec k` mapping to `t`; then
`dim_t(T_x) = dim_{t'}(T ×_X Spec k)`. Such a `t'` exists by
Properties of Stacks, Lemma 100.4.3. -/
@[stacks 0DRG] #check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : T.toGroupoids ⟶ X) [LocallyOfFiniteType f]
    (t : AlgebraicSpace.Points T), WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_eq :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : T.toGroupoids ⟶ X) [LocallyOfFiniteType f]
    (t : AlgebraicSpace.Points T) (w : RelativeDimensionChoice f t),
    fiberDimensionAt f t = w.dimension)

#check (AlgebraicGeometry.AlgebraicStack.exists_relativeDimensionChoice :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : T.toGroupoids ⟶ X) (t : AlgebraicSpace.Points T),
    Nonempty (RelativeDimensionChoice f t))

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.dimension :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t), WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.dimension_def :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    w.dimension = AlgebraicSpace.dimensionAt w.fiberPoint)

end AlgebraicGeometry.AlgebraicStack
