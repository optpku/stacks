/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Lemma_100_4_3_Comparison
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiberDimension

/-! Typed compatibility checks for relative dimensions and representing fibres. -/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Equivalent.ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    {p q : AlgebraicSpace.FieldValuedPoint F}
    (h : AlgebraicSpace.FieldValuedPoint.Equivalent p q),
    FieldValuedPoint.Equivalent (FieldValuedPoint.ofAlgebraicSpace p)
      (FieldValuedPoint.ofAlgebraicSpace q))

#check (AlgebraicGeometry.AlgebraicStack.Points.ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (x : AlgebraicSpace.Points F),
    Points F.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.Points.ofAlgebraicSpace_mk :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F),
    Points.ofAlgebraicSpace (AlgebraicSpace.Points.mk p) =
      Points.mk (FieldValuedPoint.ofAlgebraicSpace p))

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : T.toGroupoids ⟶ X) (t : AlgebraicSpace.Points T),
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.projection :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    w.fiber ⟶ T)

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.projection_spec :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    AlgebraicSpace.Points.map w.projection w.fiberPoint = t)

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.dimension :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.dimension_def :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    w.dimension = AlgebraicSpace.dimensionAt w.fiberPoint)

#check (AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.spec :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}
    (w : RelativeDimensionChoice f t),
    Points.mk w.point = Points.map f (Points.ofAlgebraicSpace t) ∧
      AlgebraicSpace.Points.map w.projection w.fiberPoint = t)

#check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T),
    WithBot ℕ∞)

#check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_eq :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T)
    (w : RelativeDimensionChoice f t),
    fiberDimensionAt f t = w.dimension)

#check (AlgebraicGeometry.AlgebraicStack.exists_relativeDimensionChoice :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    (t : AlgebraicSpace.Points T),
    Nonempty (RelativeDimensionChoice f t))

#check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_iff_relativeDimensionAt :
  ∀ {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (d : ℕ) (t : AlgebraicSpace.Points T),
    AlgebraicSpace.RelativeDimensionAt φ d t ↔
      fiberDimensionAt (AlgebraicSpace.toGroupoids.map φ) t =
        (d : WithBot ℕ∞))

end AlgebraicGeometry.AlgebraicStack
