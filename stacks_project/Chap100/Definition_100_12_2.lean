/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 100.12.2: let `X` be a locally Noetherian algebraic stack over a scheme `S`.
Let `x` be a point of `|X|`. For a presentation `P : Presentation X` (Definition 94.16.5)
whose object space is a scheme and a point `u` mapping to `x`, the dimension
`dimensionAt x` of `X` at `x` is the element of `ℤ ∪ {∞}` given by
`dimensionDiff (dimensionAt u) (fiberDimensionAt s (e u))`, equivalently
`Presentation.dimensionDiffAt`, in the notation of Lemma 100.12.1. -/
@[stacks 0AFN] #check (AlgebraicGeometry.AlgebraicStack.dimensionAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X],
    AlgebraicStack.Points X → EInt)

#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X]
    (x : AlgebraicStack.Points X) (P : AlgebraicStack.Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left),
    AlgebraicStack.Points.map
        (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
        (AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.ofAlgebraicSpace p)) = x →
    AlgebraicStack.dimensionAt x =
      AlgebraicStack.dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))))

#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq_top_or_int :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X),
    AlgebraicStack.dimensionAt x = ⊤ ∨ ∃ n : ℤ, AlgebraicStack.dimensionAt x = (n : EInt))
