/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Finite-type points of algebraic stacks, first characterization

A point of an algebraic stack is represented by a locally-of-finite-type
morphism from the spectrum of a field if and only if it is the image of a
closed point under a smooth morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X)

/-- There exists a field-valued point representing `x` whose morphism into `X` is
locally of finite type. -/
def existsLocallyOfFiniteTypeFieldValuedPoint : Prop :=
  ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x

/-- `existsLocallyOfFiniteTypeFieldValuedPoint x` means some morphism
`Spec(k) ⟶ X` is locally of finite type and represents `x`. -/
theorem existsLocallyOfFiniteTypeFieldValuedPoint_iff :
    existsLocallyOfFiniteTypeFieldValuedPoint x ↔
      ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

namespace existsLocallyOfFiniteTypeFieldValuedPoint

/-- A field-valued point of `X` whose morphism is locally of finite type and
whose class is `x` witnesses `existsLocallyOfFiniteTypeFieldValuedPoint x`. -/
theorem of {p : FieldValuedPoint X} [LocallyOfFiniteType p.hom]
    (hx : Points.mk p = x) : existsLocallyOfFiniteTypeFieldValuedPoint x :=
  sorry

/-- `existsLocallyOfFiniteTypeFieldValuedPoint x` supplies a field-valued point
representing `x` whose morphism into `X` is locally of finite type. -/
theorem spec (h : existsLocallyOfFiniteTypeFieldValuedPoint x) :
    ∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x :=
  sorry

end existsLocallyOfFiniteTypeFieldValuedPoint

/-- There exists a scheme `U` over `S`, a closed point of `U`, and a smooth
morphism from `GroupoidsOver.slice U` to `X` sending that point to `x`. -/
def existsSmoothClosedPoint : Prop :=
  ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
    u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x

/-- `existsSmoothClosedPoint x` means some smooth morphism
`φ : GroupoidsOver.slice U ⟶ X` from a scheme over `S` sends a closed point of
`U` to `x`. -/
theorem existsSmoothClosedPoint_iff :
    existsSmoothClosedPoint x ↔
      ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
        u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x :=
  sorry

namespace existsSmoothClosedPoint

/-- A smooth morphism from a scheme over `S` sending a closed point to `x`
witnesses `existsSmoothClosedPoint x`. -/
theorem of {U : Over S} {u : U.left} {φ : GroupoidsOver.slice U ⟶ X}
    (hu : u ∈ closedPoints U.left) [Groupoids.Hom.Smooth φ]
    (hx : Points.mapSlice φ u = x) : existsSmoothClosedPoint x :=
  sorry

/-- `existsSmoothClosedPoint x` supplies a scheme over `S`, a closed point of
that scheme, and a smooth morphism to `X` sending the closed point to `x`. -/
theorem spec (h : existsSmoothClosedPoint x) :
    ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
      u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x :=
  sorry

end existsSmoothClosedPoint

/-- Lemma 101.18.1: Let `X` be an algebraic stack. Let `x ∈ |X|`. The following
are equivalent: there exists a morphism `Spec(k) ⟶ X` which is locally of
finite type and represents `x`; and there exists a scheme `U`, a closed point
`u ∈ U`, and a smooth morphism `φ : U ⟶ X` such that `φ(u) = x`. -/
@[stacks 06FX]
theorem existsLocallyOfFiniteTypeFieldValuedPoint_iff_existsSmoothClosedPoint :
    existsLocallyOfFiniteTypeFieldValuedPoint x ↔ existsSmoothClosedPoint x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
