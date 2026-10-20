/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap89.Definition_89_4_1_PointBlowup

/-!
# Finite sequences of closed-point blowups of algebraic spaces

A finite composable sequence of ordinary blowups at closed points of decent
algebraic spaces, together with the composite morphism and the predicate that
every center lies over a specified subset of the initial space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X' ⟶ X` is a blowup of the decent algebraic space `X` at
the closed point `p` when the inverse image of the residue-field closed
subspace is an effective Cartier divisor and `f` is terminal among morphisms
to `X` with that property. -/
def IsPointBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsDecent X]
    (f : X' ⟶ X) (p : Points X) (hp : p ∈ closedPoints (Points X)) : Prop :=
  (ClosedSubspace.ofClosedPoint p hp).pullbackDefined f ∧
    ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
      (ClosedSubspace.ofClosedPoint p hp).pullbackDefined g →
        ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

/-- Being a blowup at a closed point is the universal property of blowing up
the residue-field closed subspace of that point. -/
theorem isPointBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsDecent X] (f : X' ⟶ X) (p : Points X)
    (hp : p ∈ closedPoints (Points X)) :
    IsPointBlowup f p hp ↔
      (ClosedSubspace.ofClosedPoint p hp).pullbackDefined f ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          (ClosedSubspace.ofClosedPoint p hp).pullbackDefined g →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g :=
  sorry

/-- A finite composable sequence of blowups at closed points, indexed by its
initial and terminal algebraic spaces. -/
inductive PointBlowupSequence {S : Scheme.{u}} :
    AlgebraicSpace S → AlgebraicSpace S → Type (u + 1) where
  /-- The empty closed-point blowup sequence. -/
  | nil (X : AlgebraicSpace S) : PointBlowupSequence X X
  /-- Prepend the blowup of a closed point of a decent algebraic space. -/
  | cons {X X' Y : AlgebraicSpace S} [IsDecent X] [IsDecent X']
      (p : Points X) (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
      (h_blowup : IsPointBlowup f p hp)
      (tail : PointBlowupSequence X' Y) : PointBlowupSequence X Y

namespace PointBlowupSequence

/-- The number of blowups in a finite closed-point blowup sequence. -/
def length {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) : ℕ :=
  match s with
  | nil _ => 0
  | cons _ _ _ _ tail => tail.length + 1

/-- The empty closed-point blowup sequence has length zero. -/
theorem length_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).length = 0 :=
  sorry

/-- Prepending one closed-point blowup increases the sequence length by one. -/
theorem length_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y) :
    (cons p hp f h_blowup tail).length = tail.length + 1 :=
  sorry

/-- The composite morphism from the terminal space of a closed-point blowup
sequence to its initial space. -/
def toSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) : Y ⟶ X :=
  match s with
  | nil _ => 𝟙 _
  | cons _ _ f _ tail => tail.toSource ≫ f

/-- The composite of an empty closed-point blowup sequence is the identity. -/
theorem toSource_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).toSource = 𝟙 X :=
  sorry

/-- The composite of a nonempty closed-point blowup sequence is the tail
composite followed by its first blowup. -/
theorem toSource_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y) :
    (cons p hp f h_blowup tail).toSource = tail.toSource ≫ f :=
  sorry

/-- Concatenate two finite closed-point blowup sequences. -/
def append {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) (t : PointBlowupSequence Y Z) :
    PointBlowupSequence X Z :=
  match s with
  | nil _ => t
  | cons p hp f h_blowup s' => cons p hp f h_blowup (s'.append t)

/-- The length of a concatenation is the sum of the lengths. -/
theorem length_append {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z) :
    (head.append tail).length = head.length + tail.length :=
  sorry

/-- The composite of a concatenation is the composite of the second sequence
followed by the composite of the first. -/
theorem toSource_append {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z) :
    (head.append tail).toSource = tail.toSource ≫ head.toSource :=
  sorry

/-- Every center in a finite point-blowup sequence lies over the specified
subset of its initial space. -/
def EveryCenterOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : PointBlowupSequence X Y) (T : Set (Points X)) : Prop :=
  match s with
  | nil _ => True
  | cons p _ f _ tail => p ∈ T ∧ tail.EveryCenterOver (Points.map f ⁻¹' T)

/-- An empty point-blowup sequence has no centers. -/
theorem everyCenterOver_nil {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) : (nil X).EveryCenterOver T ↔ True :=
  sorry

/-- Center support for a nonempty point-blowup sequence consists of support
for its first center and support for the remaining centers after pulling back
the specified subset. -/
theorem everyCenterOver_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent X'] (p : Points X)
    (hp : p ∈ closedPoints (Points X)) (f : X' ⟶ X)
    (h_blowup : IsPointBlowup f p hp) (tail : PointBlowupSequence X' Y)
    (T : Set (Points X)) :
    (cons p hp f h_blowup tail).EveryCenterOver T ↔
      p ∈ T ∧ tail.EveryCenterOver (Points.map f ⁻¹' T) :=
  sorry

/-- Center support for a concatenated point-blowup sequence is equivalent to
support for the first sequence and support for the second sequence over the
inverse image of the original subset. -/
theorem everyCenterOver_append {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (head : PointBlowupSequence X Y) (tail : PointBlowupSequence Y Z)
    (T : Set (Points X)) :
    (head.append tail).EveryCenterOver T ↔
      head.EveryCenterOver T ∧
        tail.EveryCenterOver (Points.map head.toSource ⁻¹' T) :=
  sorry

end PointBlowupSequence

end AlgebraicGeometry.AlgebraicSpace
