/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian

/-!
# Dimension of a locally Noetherian algebraic stack

The dimension of a locally Noetherian algebraic stack is the supremum of its
dimensions at points. Local dimensions are differences `dim_u(U) - dim_{e(u)}(R_u)`
along presentations, valued in `EInt` so that they may be negative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
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
  sorry

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
  sorry

/-- The field-valued point of the slice of `U` associated to a scheme point of `U`. -/
def FieldValuedPoint.ofResidue {S : Scheme.{u}} {U : Over S} (u : U.left) :
    FieldValuedPoint (GroupoidsOver.slice U) :=
  of (U.left.residueField u) (U.left.fromSpecResidueField u ≫ U.hom)
    (overMap (Over.homMk (U.left.fromSpecResidueField u)))

/-- The structure morphism of `ofResidue u` is the residue-field map of `u` over `S`. -/
theorem FieldValuedPoint.ofResidue_structureHom {S : Scheme.{u}} {U : Over S} (u : U.left) :
    (FieldValuedPoint.ofResidue u).structureHom =
      U.left.fromSpecResidueField u ≫ U.hom :=
  sorry

/-- The morphism of `ofResidue u` is `overMap` of the residue-field map of `u`. -/
theorem FieldValuedPoint.ofResidue_hom {S : Scheme.{u}} {U : Over S} (u : U.left) :
    (FieldValuedPoint.ofResidue u).hom =
      overMap (Over.homMk (U.left.fromSpecResidueField u)) :=
  sorry

namespace Points

/-- The image in `|X|` of a scheme point of `U` along a morphism `slice U ⟶ X`. -/
def mapSlice {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) : Points X :=
  mk ((FieldValuedPoint.ofResidue u).map p)

/-- `mapSlice p u` is the class of the postcomposition of the residue-field point of `u`. -/
theorem mapSlice_mk {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) :
    mapSlice p u = mk ((FieldValuedPoint.ofResidue u).map p) :=
  sorry

end Points

/-- The field-valued point of `F.toGroupoids` associated to a field-valued point of an
algebraic space `F`. -/
def FieldValuedPoint.ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) : FieldValuedPoint F.toGroupoids :=
  of p.K p.structureHom
    ((AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫ AlgebraicSpace.toGroupoids.map p.hom)

/-- `ofAlgebraicSpace` preserves the structure morphism to `S`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_structureHom {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).structureHom = p.structureHom :=
  sorry

/-- The morphism of `ofAlgebraicSpace p` is the slice comparison followed by `toGroupoids.map`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_hom {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).hom =
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
        AlgebraicSpace.toGroupoids.map p.hom :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack at a point, as the supremum of
presentation differences `dimensionAt u - fiberDimensionAt s (e u)` along points of the
object space mapping to `x`. -/
noncomputable def dimensionAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) : EInt :=
  ⨆ (P : Presentation X) (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (_hx : Points.map (P.groupoid.atlas ≫ P.hom)
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
    (hx : Points.map (P.groupoid.atlas ≫ P.hom)
        (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x) :
    dimensionAt x =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))) :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack is the supremum of its dimensions
at points. -/
theorem dimension_eq_iSup_dimensionAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⨆ x : Points X, dimensionAt x :=
  sorry

/-- Unfolding of `dimension` as a supremum of `dimensionAt`. -/
theorem dimension_def {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    dimension X = ⨆ x : Points X, dimensionAt x :=
  sorry

/-- On the slice of a locally Noetherian scheme, the stack dimension recovers the usual
topological Krull dimension after embedding into `EInt`. -/
theorem dimension_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    dimension (GroupoidsOver.slice U) = dimensionToEInt (topologicalKrullDim U.left) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
