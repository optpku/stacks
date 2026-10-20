/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral.FiniteComponents

/-!
# Sequences of normalized blowups and resolution of surfaces

A two-dimensional Noetherian integral algebraic space has a resolution by
normalized blowups when its canonical normalization is followed by a finite
sequence of normalized point blowups, every stage is proper over the original
space, and the terminal space is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite composable sequence of normalized blowups, indexed by its initial and terminal
algebraic spaces. -/
inductive NormalizedBlowupSequence {S : Scheme.{u}} :
    AlgebraicSpace S → AlgebraicSpace S → Type (u + 1) where
  /-- The empty normalized-blowup sequence. -/
  | nil (X : AlgebraicSpace S) : NormalizedBlowupSequence X X
  /-- Prepend a normalized blowup to a sequence starting at its normalized source. -/
  | cons {X Y : AlgebraicSpace S} [IsDecent X]
      [HasFiniteIrreducibleComponentsOnCompactOpens X] (step : NormalizedBlowup X)
      (tail : NormalizedBlowupSequence step.source Y) : NormalizedBlowupSequence X Y

namespace NormalizedBlowupSequence

/-- The number of normalized blowups in a finite sequence. -/
def length {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) : ℕ :=
  match s with
  | nil _ => 0
  | @cons _ _ _ _ _ _ tail => tail.length + 1

/-- The empty normalized-blowup sequence has length zero. -/
theorem length_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).length = 0 :=
  sorry

/-- Prepending a normalized blowup increases the sequence length by one. -/
theorem length_cons {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y) :
    (cons step tail).length = tail.length + 1 :=
  sorry

/-- The composite morphism from the terminal space of a normalized-blowup sequence to its
initial space. -/
noncomputable def toSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) : Y ⟶ X :=
  match s with
  | nil _ => 𝟙 _
  | @cons _ _ _ _ _ step tail => tail.toSource ≫ step.hom

/-- The composite of an empty normalized-blowup sequence is the identity. -/
theorem toSource_nil {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (nil X).toSource = 𝟙 X :=
  sorry

/-- The composite of a nonempty normalized-blowup sequence is the tail composite followed by
its first normalized blowup. -/
theorem toSource_cons {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y) :
    (cons step tail).toSource = tail.toSource ≫ step.hom :=
  sorry

/-- `EveryTargetOver s f` says that every post-initial stage of `s`, composed with `f`, is proper
over the target of `f`. -/
def EveryTargetOver {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (s : NormalizedBlowupSequence X Y) (f : X ⟶ B) : Prop :=
  match s with
  | nil _ => True
  | @cons _ _ _ _ _ step tail =>
      Proper (step.hom ≫ f) ∧ tail.EveryTargetOver (step.hom ≫ f)

/-- An empty normalized-blowup sequence has no post-initial stages. -/
theorem everyTargetOver_nil {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) :
    (nil X).EveryTargetOver f ↔ True :=
  sorry

/-- Every post-initial stage of a nonempty sequence is proper over the base exactly when its first
target and all targets of its tail are proper over the base. -/
theorem everyTargetOver_cons {S : Scheme.{u}} {X Y B : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (step : NormalizedBlowup X) (tail : NormalizedBlowupSequence step.source Y)
    (f : X ⟶ B) :
    (cons step tail).EveryTargetOver f ↔
      Proper (step.hom ≫ f) ∧ tail.EveryTargetOver (step.hom ≫ f) :=
  sorry

end NormalizedBlowupSequence

/-- A two-dimensional Noetherian integral algebraic space has a resolution by normalized blowups
when its normalization is proper, a finite sequence of normalized point blowups has every later
stage proper over the original space, and its terminal space is regular. -/
def HasResolutionByNormalizedBlowups {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsNoetherian Y] [IsIntegral Y] (h_dim : dimension Y = 2) : Prop :=
  ∃ (Z : AlgebraicSpace S) (s : NormalizedBlowupSequence Y.normalization Z),
    Proper Y.normalizationTo ∧
      s.EveryTargetOver Y.normalizationTo ∧ IsRegular Z

/-- The resolution predicate records the normalization, every proper intermediate stage, the
finite normalized-blowup chain, and its regular terminal space. -/
theorem hasResolutionByNormalizedBlowups_iff {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [IsNoetherian Y] [IsIntegral Y] (h_dim : dimension Y = 2) :
    HasResolutionByNormalizedBlowups Y h_dim ↔
      ∃ (Z : AlgebraicSpace S) (s : NormalizedBlowupSequence Y.normalization Z),
        Proper Y.normalizationTo ∧
          s.EveryTargetOver Y.normalizationTo ∧ IsRegular Z :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
