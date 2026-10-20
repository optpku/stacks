module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Finite type points of an algebraic space

A point is of finite type when it admits a locally finite type field-valued
representative. Locally finite type morphisms preserve these points.
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

namespace LocallyOfFiniteType

/-- The image of the finite-type points under a locally finite type morphism of
algebraic spaces is contained in the finite-type points of its target. -/
theorem image_finiteTypePoints_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y :=
  sorry

/-- A locally-of-finite-type morphism of algebraic spaces sends finite-type
points to finite-type points. -/
theorem map_mem_finiteTypePoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {x : Points X}
    (hx : x ∈ finiteTypePoints X) :
    Points.map f x ∈ finiteTypePoints Y :=
  sorry

/-- A surjective locally-of-finite-type morphism of algebraic spaces maps the
finite-type points onto the finite-type points of its target. -/
theorem image_finiteTypePoints_eq_of_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] :
    Points.map f '' finiteTypePoints X = finiteTypePoints Y :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
