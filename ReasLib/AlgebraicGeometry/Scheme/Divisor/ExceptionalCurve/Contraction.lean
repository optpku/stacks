/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve

/-!
# Contractions of exceptional curves

This module records the geometric property that a morphism contracts an exceptional curve by
realizing its source as the blowup of a regular two-dimensional closed point.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism contracts an exceptional curve of the first kind to a closed point when its
target is Noetherian, it is proper, it is the blowup of that point, the target stalk there is
regular of dimension two, and the pulled-back center ideal is the exceptional curve. -/
structure IsContraction {X Y : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] (b : X ⟶ Y) (y : closedPoints Y) : Prop where
  /-- The target of a contraction is Noetherian. -/
  targetNoetherian : IsNoetherian Y
  /-- A contraction is proper. -/
  proper : IsProper b
  /-- A contraction realizes its source as the blowup of its center. -/
  blowup :
    IsBlowup b (Scheme.IdealSheafData.vanishingIdeal
      (Scheme.PointClosure.closedSubset y.1))
  /-- The local ring at the contraction center is regular. -/
  regularCenter : IsRegularLocalRing (Y.presheaf.stalk y.1)
  /-- The local ring at the contraction center has Krull dimension two. -/
  dimensionCenter : ringKrullDim (Y.presheaf.stalk y.1) = 2
  /-- The exceptional curve is the pullback of the reduced center ideal. -/
  exceptional_eq :
    E = (Scheme.IdealSheafData.vanishingIdeal
      (Scheme.PointClosure.closedSubset y.1)).comap b

namespace IsContraction

variable {X Y : Scheme.{u}} [IsNoetherian X] {E : X.IdealSheafData}
  [IsExceptionalCurveFirstKind E] {b : X ⟶ Y} {y : closedPoints Y}

/-- Build a contraction from the geometric conditions at its center. -/
def ofConditions (h_noetherian : IsNoetherian Y) (h_proper : IsProper b)
    (h_blowup : IsBlowup b (Scheme.IdealSheafData.vanishingIdeal
      (Scheme.PointClosure.closedSubset y.1)))
    (h_regular : IsRegularLocalRing (Y.presheaf.stalk y.1))
    (h_dimension : ringKrullDim (Y.presheaf.stalk y.1) = 2)
    (h_exceptional : E = (Scheme.IdealSheafData.vanishingIdeal
      (Scheme.PointClosure.closedSubset y.1)).comap b) : IsContraction E b y :=
  ⟨h_noetherian, h_proper, h_blowup, h_regular, h_dimension, h_exceptional⟩

/-- A contraction maps the support of its exceptional curve to its center. -/
theorem mapsToCenter (h : IsContraction E b y) :
    Set.MapsTo b E.support ({y.1} : Set Y) := sorry

/-- Every morphism that maps an exceptional curve of the first kind to one point factors uniquely
through any contraction of that curve. -/
theorem existsUnique_factor {X X' Y : Scheme.{u}} [IsNoetherian X]
    {E : X.IdealSheafData} [IsExceptionalCurveFirstKind E]
    {b : X ⟶ X'} {x : closedPoints X'} (h : IsContraction E b x)
    (φ : X ⟶ Y) (y : Y) (h_maps : Set.MapsTo φ E.support ({y} : Set Y)) :
    ∃! g : X' ⟶ Y, b ≫ g = φ := sorry

/-- Two contractions of the same exceptional curve admit a unique isomorphism
    commuting with their contraction morphisms. -/
theorem existsUnique_iso {X Y₁ Y₂ : Scheme.{u}} [IsNoetherian X]
    {E : X.IdealSheafData} [IsExceptionalCurveFirstKind E]
    {b₁ : X ⟶ Y₁} {y₁ : closedPoints Y₁} (h₁ : IsContraction E b₁ y₁)
    {b₂ : X ⟶ Y₂} {y₂ : closedPoints Y₂} (h₂ : IsContraction E b₂ y₂) :
    ∃! e : Y₁ ≅ Y₂, b₁ ≫ e.hom = b₂ := sorry

end IsContraction

/-- A contraction is characterized by Noetherianity of the target, properness, the point-blowup
property, regularity and dimension two at the center, and the exceptional-ideal equality. -/
theorem isContraction_iff {X Y : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ Y) (y : closedPoints Y) :
    IsContraction E b y ↔
      IsNoetherian Y ∧ IsProper b ∧
        IsBlowup b (Scheme.IdealSheafData.vanishingIdeal
          (Scheme.PointClosure.closedSubset y.1)) ∧
        IsRegularLocalRing (Y.presheaf.stalk y.1) ∧
        ringKrullDim (Y.presheaf.stalk y.1) = 2 ∧
        E = (Scheme.IdealSheafData.vanishingIdeal
          (Scheme.PointClosure.closedSubset y.1)).comap b := sorry

end AlgebraicGeometry
