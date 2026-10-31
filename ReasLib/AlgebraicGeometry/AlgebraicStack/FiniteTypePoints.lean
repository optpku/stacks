/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType.Composition

/-!
# Finite-type points of algebraic stacks

A finite-type point admits a locally-of-finite-type field-valued representative.
Locally-of-finite-type morphisms of algebraic stacks preserve finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A point of an algebraic stack is of finite type if it is represented by a
morphism `Spec k ⟶ X` that is locally of finite type. -/
def IsFiniteTypePoint {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x

/-- A point is of finite type if and only if some field-valued representative is
locally of finite type. -/
theorem isFiniteTypePoint_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (x : Points X) :
    IsFiniteTypePoint x ↔
      ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  Iff.rfl

namespace IsFiniteTypePoint

/-- The class of a locally-of-finite-type field-valued point is a finite-type
point. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) [LocallyOfFiniteType p.hom] :
    IsFiniteTypePoint (Points.mk p) :=
  ⟨p, inferInstance, rfl⟩

/-- A finite-type point is represented by some locally-of-finite-type
field-valued point. -/
theorem exists_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : IsFiniteTypePoint x) :
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  hx

end IsFiniteTypePoint

/-- The set of finite-type points of an algebraic stack. -/
def finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Set (Points X) :=
  {x | IsFiniteTypePoint x}

/-- Membership in `finiteTypePoints X` is the finite-type point property. -/
theorem mem_finiteTypePoints_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ finiteTypePoints X ↔ IsFiniteTypePoint x :=
  Iff.rfl

namespace LocallyOfFiniteType

/-- The image of the finite-type points under a locally-of-finite-type morphism
of algebraic stacks is contained in the finite-type points of its target. -/
@[stacks 06G0]
theorem image_finiteTypePoints_subset {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] :
    Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hx
  letI : LocallyOfFiniteType p.hom := hp
  exact ⟨p.map f, comp p.hom f, rfl⟩

/-- A locally-of-finite-type morphism of algebraic stacks sends finite-type
points to finite-type points. -/
theorem map_mem_finiteTypePoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    {x : Points X} (hx : x ∈ finiteTypePoints X) :
    Points.map f x ∈ finiteTypePoints Y :=
  image_finiteTypePoints_subset f ⟨x, hx, rfl⟩

/-- A surjective locally-of-finite-type morphism of algebraic stacks maps its
finite-type points onto the finite-type points of its target. -/
@[stacks 06G1]
theorem image_finiteTypePoints_eq_of_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] :
    Points.map f '' finiteTypePoints X = finiteTypePoints Y :=
  sorry

/-- Membership in the image of finite-type points along a surjective
locally-of-finite-type morphism is equivalent to being a finite-type point of
the target. -/
theorem mem_image_finiteTypePoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    {y : Points Y} :
    y ∈ Points.map f '' finiteTypePoints X ↔ y ∈ finiteTypePoints Y := by
  rw [image_finiteTypePoints_eq_of_surjective f]

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicStack
