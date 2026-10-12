/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Finite-type points of an algebraic stack

A point of an algebraic stack is of finite type when it is represented by a
morphism `Spec k ⟶ X` that is locally of finite type.
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
  sorry

namespace IsFiniteTypePoint

/-- The class of a locally-of-finite-type field-valued point is a finite-type
point. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) [LocallyOfFiniteType p.hom] :
    IsFiniteTypePoint (Points.mk p) :=
  sorry

/-- A finite-type point is represented by some locally-of-finite-type
field-valued point. -/
theorem exists_fieldValuedPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : IsFiniteTypePoint x) :
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

end IsFiniteTypePoint

/-- The set of finite-type points of an algebraic stack. -/
def finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Set (Points X) :=
  {x | IsFiniteTypePoint x}

/-- Membership in `finiteTypePoints X` is the finite-type point property. -/
theorem mem_finiteTypePoints_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ finiteTypePoints X ↔ IsFiniteTypePoint x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
