/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Lemma 72.16.2

Finite separable field-valued points are dense on an algebraic space smooth over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of an algebraic space over a field is a finite separable field point if it is
the image of a morphism `Spec k' ⟶ X` for a finite separable field extension `k'/k`. -/
def IsFiniteSeparableFieldPoint {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (x : Points X) : Prop :=
  ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
    FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      ∃ p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X,
        fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p = x

/-- A point is a finite separable field point if and only if it is the image of a morphism
`Spec k' ⟶ X` for a finite separable field extension `k'/k`. -/
theorem isFiniteSeparableFieldPoint_iff {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (x : Points X) :
    IsFiniteSeparableFieldPoint x ↔
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
          ∃ p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X,
            fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p = x :=
  sorry

namespace IsFiniteSeparableFieldPoint

/-- The image of a morphism `Spec k' ⟶ X` along a finite separable extension `k'/k` is a
finite separable field point. -/
theorem of_hom {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (p : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⟶ X) :
    IsFiniteSeparableFieldPoint
      (fieldPointsToPoints (Spec.map (CommRingCat.ofHom (algebraMap k k'))) p) :=
  sorry

end IsFiniteSeparableFieldPoint

/-- Lemma 72.16.2: let `k` be a field, and let `X` be an algebraic space smooth over
`Spec k`. The set of points of `X` which are images of morphisms `Spec k' ⟶ X` with
`k'/k` finite separable is dense in the space of points of `X`. -/
@[stacks 07W4]
theorem dense_finiteSeparableFieldPoints {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Smooth (toBase X)] :
    Dense (setOf fun x : Points X ↦ IsFiniteSeparableFieldPoint x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
