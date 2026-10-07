module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Finite type points of an algebraic space

A point of an algebraic space `X` over a scheme `S` is of finite type when it
is represented by a morphism `Spec(k) ⟶ X` that is locally of finite type,
Stacks Lemma 67.25.1 (1) and Definition 67.25.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of an algebraic space is of finite type if it is represented by a
morphism `Spec(k) ⟶ X` that is locally of finite type. -/
def IsFiniteTypePoint {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Prop :=
  ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x

/-- A point is of finite type if and only if some field-valued representative is
locally of finite type. -/
theorem isFiniteTypePoint_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    IsFiniteTypePoint x ↔
      ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

namespace IsFiniteTypePoint

/-- The class of a locally-of-finite-type field-valued point is a finite-type
point. -/
theorem of_fieldValuedPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPoint X) [LocallyOfFiniteType p.hom] :
    IsFiniteTypePoint (Points.mk p) :=
  sorry

/-- A finite-type point is represented by some locally-of-finite-type
field-valued point. -/
theorem exists_fieldValuedPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {x : Points X} (hx : IsFiniteTypePoint x) :
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

end IsFiniteTypePoint

/-- The set of finite-type points of an algebraic space. -/
def finiteTypePoints {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | IsFiniteTypePoint x}

/-- Membership in `finiteTypePoints X` is the finite-type point property. -/
theorem mem_finiteTypePoints_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {x : Points X} :
    x ∈ finiteTypePoints X ↔ IsFiniteTypePoint x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
