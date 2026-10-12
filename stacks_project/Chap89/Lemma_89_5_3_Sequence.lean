/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_5_Normalization
public import stacks_project.Chap89.Lemma_89_4_2_PointBlowupSequence

/-!
# Finite sequences of normalized blowups of algebraic spaces

A finite composable sequence of normalized blowups at closed points of decent
algebraic spaces. Each step is an ordinary closed-point blowup
`IsPointBlowup`, followed by the absolute normalization of that blowup space,
as in Definition 89.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite composable sequence of normalized blowups at closed points, indexed
by its initial and terminal algebraic spaces. -/
inductive NormalizedBlowupSequence {S : Scheme.{u}} :
    AlgebraicSpace S → AlgebraicSpace S → Type (u + 1) where
  /-- The empty normalized-blowup sequence. -/
  | nil (X : AlgebraicSpace S) : NormalizedBlowupSequence X X
  /-- Prepend the normalized blowup of a decent algebraic space at a closed
  point: an ordinary closed-point blowup, followed by absolute normalization
  of that blowup space. -/
  | cons {X X' Y : AlgebraicSpace S} [IsDecent X]
      [HasFiniteIrreducibleComponentsOnCompactOpens X]
      [HasFiniteIrreducibleComponentsOnCompactOpens X']
      (p : Points X) (hp : p ∈ closedPoints (Points X)) (toBlowup : X' ⟶ X)
      (h_blowup : IsPointBlowup toBlowup p hp)
      (tail : NormalizedBlowupSequence (normalization X') Y) :
      NormalizedBlowupSequence X Y

namespace NormalizedBlowupSequence

/-- The number of normalized blowups in a finite sequence. -/
def length {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) : ℕ :=
  match s with
  | nil _ => 0
  | cons _ _ _ _ tail => tail.length + 1

/-- The empty normalized-blowup sequence has length zero. -/
theorem length_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).length = 0 :=
  sorry

/-- Prepending a normalized blowup increases the sequence length by one. -/
theorem length_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X']
    (p : Points X) (hp : p ∈ closedPoints (Points X)) (toBlowup : X' ⟶ X)
    (h_blowup : IsPointBlowup toBlowup p hp)
    (tail : NormalizedBlowupSequence (normalization X') Y) :
    (cons p hp toBlowup h_blowup tail).length = tail.length + 1 :=
  sorry

/-- The composite morphism from the terminal space of a normalized-blowup
sequence to its initial space. -/
noncomputable def toSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) : Y ⟶ X :=
  match s with
  | nil _ => 𝟙 _
  | cons _ _ toBlowup _ tail => tail.toSource ≫ (normalizationTo _ ≫ toBlowup)

/-- The composite of an empty normalized-blowup sequence is the identity. -/
theorem toSource_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).toSource = 𝟙 X :=
  sorry

/-- The composite of a nonempty normalized-blowup sequence is the tail composite
followed by normalization of the ordinary blowup and then that blowup. -/
theorem toSource_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X']
    (p : Points X) (hp : p ∈ closedPoints (Points X)) (toBlowup : X' ⟶ X)
    (h_blowup : IsPointBlowup toBlowup p hp)
    (tail : NormalizedBlowupSequence (normalization X') Y) :
    (cons p hp toBlowup h_blowup tail).toSource =
      tail.toSource ≫ (normalizationTo X' ≫ toBlowup) :=
  sorry

/-- Every center in a finite normalized-blowup sequence lies over the specified
subset of its initial space. -/
def EveryCenterOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) (T : Set (Points X)) : Prop :=
  match s with
  | nil _ => True
  | cons p _ toBlowup _ tail =>
      p ∈ T ∧
        tail.EveryCenterOver (Points.map (normalizationTo _ ≫ toBlowup) ⁻¹' T)

/-- An empty normalized-blowup sequence has no centers. -/
theorem everyCenterOver_nil {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) : (nil X).EveryCenterOver T ↔ True :=
  sorry

/-- Center support for a nonempty normalized-blowup sequence consists of support
for its first center and support for the remaining centers after pulling back
the specified subset along the normalized blowup morphism. -/
theorem everyCenterOver_cons {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsDecent X] [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X']
    (p : Points X) (hp : p ∈ closedPoints (Points X)) (toBlowup : X' ⟶ X)
    (h_blowup : IsPointBlowup toBlowup p hp)
    (tail : NormalizedBlowupSequence (normalization X') Y)
    (T : Set (Points X)) :
    (cons p hp toBlowup h_blowup tail).EveryCenterOver T ↔
      p ∈ T ∧
        tail.EveryCenterOver
          (Points.map (normalizationTo X' ≫ toBlowup) ⁻¹' T) :=
  sorry

end NormalizedBlowupSequence

end AlgebraicGeometry.AlgebraicSpace
