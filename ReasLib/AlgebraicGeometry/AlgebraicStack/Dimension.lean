/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Induced

/-!
# Dimension of a locally Noetherian algebraic stack

The dimension of a locally Noetherian algebraic stack is the supremum of its
dimensions at points. Local dimensions are differences `dim_u(U) - dim_{e(u)}(R_u)`
along presentations, valued in `EInt` so that they may be negative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Convert a `WithBot ℕ∞` dimension to an extended integer. -/
def dimensionToEInt (d : WithBot ℕ∞) : EInt :=
  WithBot.map (WithTop.map Int.ofNat) d

/-- `dimensionToEInt` is `WithBot.map` of `WithTop.map Int.ofNat`. -/
theorem dimensionToEInt_apply (d : WithBot ℕ∞) :
    dimensionToEInt d = WithBot.map (WithTop.map Int.ofNat) d :=
  rfl

/-- The difference of two `WithBot ℕ∞` dimensions, as an extended integer. -/
def dimensionDiff (a b : WithBot ℕ∞) : EInt :=
  match a, b with
  | none, _ => ⊥
  | some _, none => ⊤
  | some none, some none => ⊤
  | some none, some (some _) => ⊤
  | some (some _), some none => ⊥
  | some (some n), some (some m) => ((n : ℤ) - (m : ℤ) : EInt)

/-- On finite values, `dimensionDiff` is ordinary integer subtraction. -/
theorem dimensionDiff_nat (n m : ℕ) :
    dimensionDiff n m = ((n : ℤ) - (m : ℤ) : EInt) :=
  rfl

/-- The dimension of a locally Noetherian algebraic stack at a point, as the supremum of
presentation differences `dimensionAt u - fiberDimensionAt s (e u)` along points of the
object space mapping to `x`. -/
noncomputable def dimensionAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) : EInt :=
  ⨆ (P : Presentation X) (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hx : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
        (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x),
    dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
      (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
        (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)))

/-- The dimension of a locally Noetherian algebraic stack, as the supremum of its dimensions
at points of `|X|`. -/
noncomputable def dimension {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] : EInt :=
  ⨆ x : Points X, dimensionAt x

/-- The dimension at a point equals the presentation difference
`dimensionAt u - fiberDimensionAt s (e u)` for any presentation through that point. -/
theorem dimensionAt_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hx : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
        (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x) :
    dimensionAt x =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))) :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack at a point is positive infinity
or an integer. -/
theorem dimensionAt_eq_top_or_int {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) :
    dimensionAt x = ⊤ ∨ ∃ n : ℤ, dimensionAt x = (n : EInt) :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack is the supremum of its dimensions
at points. -/
theorem dimension_eq_iSup_dimensionAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⨆ x : Points X, dimensionAt x :=
  rfl

/-- On the slice of a locally Noetherian scheme, the stack dimension recovers the usual
topological Krull dimension after embedding into `EInt`. -/
theorem dimension_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    dimension (GroupoidsOver.slice U) = dimensionToEInt (topologicalKrullDim U.left) :=
  sorry

namespace Presentation

/-- The presentation difference is the dimension of the object space at a point minus
the dimension of the source fibre at its identity arrow. -/
noncomputable def dimensionDiffAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) : EInt :=
  dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
    (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
      (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)))

/-- The presentation difference unfolds to the difference of the object-space dimension
and the source-fibre dimension at the identity arrow. -/
theorem dimensionDiffAt_def {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) :
    P.dimensionDiffAt p =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))) :=
  rfl

/-- For a locally Noetherian algebraic stack, presentation differences at points mapping
to the same stack point agree. -/
theorem dimensionDiffAt_independent {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P P' : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (p' : AlgebraicSpace.FieldValuedPoint P'.groupoid.U.left)
    (hp : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x)
    (hp' : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P'.groupoid ≫ P'.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p')) = x) :
    P.dimensionDiffAt p = P'.dimensionDiffAt p' := by
  calc
    P.dimensionDiffAt p = dimensionAt x := (dimensionAt_eq x P p hp).symm
    _ = P'.dimensionDiffAt p' := dimensionAt_eq x P' p' hp'

/-- A presentation difference at a point of a locally Noetherian algebraic stack is
positive infinity or an integer. -/
theorem dimensionDiffAt_eq_top_or_int {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hp : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x) :
    P.dimensionDiffAt p = ⊤ ∨ ∃ n : ℤ, P.dimensionDiffAt p = n := by
  have h : dimensionAt x = P.dimensionDiffAt p := dimensionAt_eq x P p hp
  rw [← h]
  exact dimensionAt_eq_top_or_int x

/-- The local dimension of the source fibre of a presentation at the identity arrow
of an object-space point is a natural number. -/
theorem fiberDimensionAt_identity_eq_nat {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) :
    ∃ n : ℕ,
      AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)) =
        n :=
  sorry

end Presentation

end AlgebraicGeometry.AlgebraicStack
