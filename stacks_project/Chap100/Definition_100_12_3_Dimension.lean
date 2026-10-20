module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
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
# Dimension API compatibility checks

The dimension and point-comparison API is supplied by its mathematical owners.
The source-facing imports remain available to existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.dimensionToEInt :
    ∀ (d : WithBot ℕ∞),
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.dimensionToEInt_apply :
    ∀ (d : WithBot ℕ∞),
    dimensionToEInt d = WithBot.map (WithTop.map Int.ofNat) d)

#check (AlgebraicGeometry.AlgebraicStack.dimensionDiff :
    ∀ (a b : WithBot ℕ∞),
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.dimensionDiff_nat :
    ∀ (n m : ℕ),
    dimensionDiff n m = ((n : ℤ) - (m : ℤ) : EInt))

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofResidue :
    ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    FieldValuedPoint (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofResidue_structureHom :
    ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    (FieldValuedPoint.ofResidue u).structureHom =
      U.left.fromSpecResidueField u ≫ U.hom)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofResidue_hom :
    ∀ {S : Scheme.{u}} {U : Over S} (u : U.left),
    (FieldValuedPoint.ofResidue u).hom =
      overMap (Over.homMk (U.left.fromSpecResidueField u)))

#check (AlgebraicGeometry.AlgebraicStack.Points.mapSlice :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
    Points X)

#check (AlgebraicGeometry.AlgebraicStack.Points.mapSlice_mk :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
    Points.mapSlice p u = Points.mk ((FieldValuedPoint.ofResidue u).map p))

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofAlgebraicSpace :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F),
    FieldValuedPoint F.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofAlgebraicSpace_structureHom :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F),
    (FieldValuedPoint.ofAlgebraicSpace p).structureHom = p.structureHom)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.ofAlgebraicSpace_hom :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F),
    (FieldValuedPoint.ofAlgebraicSpace p).hom =
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
        AlgebraicSpace.toGroupoids.map p.hom)

#check (AlgebraicGeometry.AlgebraicStack.dimensionAt :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X),
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.dimension :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X],
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X) (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hx : Points.map (GroupoidAlgebraicSpace.SmallQuotient.atlas P.groupoid ≫ P.hom)
        (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x),
    dimensionAt x =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))))

#check (AlgebraicGeometry.AlgebraicStack.dimension_eq_iSup_dimensionAt :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X],
    dimension X = ⨆ x : Points X, dimensionAt x)

#check (AlgebraicGeometry.AlgebraicStack.dimension_slice :
    ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left],
    dimension (GroupoidsOver.slice U) = dimensionToEInt (topologicalKrullDim U.left))

end AlgebraicGeometry.AlgebraicStack
