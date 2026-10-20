module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints

/-!
# Finite separable field-valued points

Finite separable field-valued points of algebraic spaces and their basic
specification and introduction properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of an algebraic space over a field is represented by a finite
separable extension of the field. -/
def IsFiniteSeparableFieldPoint {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (x : Points X) : Prop :=
  ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
    FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      ∃ p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X,
        fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p = x

/-- A point is represented by a finite separable extension exactly when the
corresponding field-valued morphism exists. -/
theorem isFiniteSeparableFieldPoint_iff {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (x : Points X) :
    IsFiniteSeparableFieldPoint x ↔
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
          ∃ p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X,
            fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p = x :=
  sorry

namespace IsFiniteSeparableFieldPoint

/-- A morphism from the spectrum of a finite separable extension determines a
finite separable field-valued point. -/
theorem of_hom {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X) :
    IsFiniteSeparableFieldPoint
      (fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p) :=
  sorry

end IsFiniteSeparableFieldPoint

end AlgebraicGeometry.AlgebraicSpace
