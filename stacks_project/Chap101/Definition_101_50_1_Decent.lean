/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Decent algebraic stacks

An algebraic stack is decent when every point is represented by a
quasi-compact morphism from the spectrum of a field. Unlike algebraic
spaces, no monomorphism hypothesis is required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is decent if every point is represented by a
quasi-compact morphism from the spectrum of a field. -/
@[mk_iff]
class IsDecent {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- Every point arises from a quasi-compact morphism `Spec(K) ⟶ X`. -/
  exists_quasiCompact :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x

namespace IsDecent

/-- A decent algebraic stack has, at every point, a quasi-compact morphism from
the spectrum of a field representing that point. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDecent X] :
    ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x :=
  sorry

/-- A choice of quasi-compact morphism `Spec(K) ⟶ X` at every point witnesses
that the algebraic stack is decent. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x) :
    IsDecent X :=
  sorry

end IsDecent

/-- The canonical slice of a scheme over `S` is a decent algebraic stack. -/
instance instIsDecent_slice {S : Scheme.{u}} (U : Over S) :
    IsDecent (GroupoidsOver.slice U) :=
  sorry

/-- The groupoid fibration of a decent algebraic space is a decent algebraic
stack. -/
instance instIsDecent_of_toGroupoids {S : Scheme.{u}} (A : AlgebraicSpace S)
    [AlgebraicSpace.IsDecent A] : IsDecent A.toGroupoids :=
  sorry

end AlgebraicGeometry.AlgebraicStack
