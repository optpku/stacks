/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
import StacksCheckRecall

/-!
# Independence of presentation differences at a point

For a locally Noetherian algebraic stack, the difference
`dim_u(U) - dim_{e(u)}(R_u)` attached to a presentation through a point of `|X|`
is independent of the presentation and of the chosen point over `x`, and takes
values in `ℤ ∪ {∞}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Presentation.dimensionDiffAt :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left),
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.dimensionDiffAt_def :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left),
    P.dimensionDiffAt p =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))))

/- Lemma 100.12.1: For a locally Noetherian algebraic stack, the presentation
difference at a point is independent of the presentation and the point over it. -/
@[stacks 0AFM] #check (AlgebraicGeometry.AlgebraicStack.Presentation.dimensionDiffAt_independent :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P P' : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (p' : AlgebraicSpace.FieldValuedPoint P'.groupoid.U.left)
    (hp : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x)
    (hp' : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P'.groupoid ≫ P'.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p')) = x),
    P.dimensionDiffAt p = P'.dimensionDiffAt p')

#check (AlgebraicGeometry.AlgebraicStack.Presentation.dimensionDiffAt_eq_top_or_int :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hp : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x),
    P.dimensionDiffAt p = ⊤ ∨ ∃ n : ℤ, P.dimensionDiffAt p = n)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.fiberDimensionAt_identity_eq_nat :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left),
    ∃ n : ℕ,
      AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)) =
        n)

end AlgebraicGeometry.AlgebraicStack
