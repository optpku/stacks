/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite composable sequence of normalized blowups, indexed by its initial and terminal
schemes. -/
inductive NormalizedBlowupSequence : Scheme.{u} → Scheme.{u} → Type (u + 1) where
  /-- The empty normalized-blowup sequence. -/
  | nil (X : Scheme.{u}) : NormalizedBlowupSequence X X
  /-- Prepend a normalized blowup to a sequence starting at its normalized source. -/
  | cons {X Y : Scheme.{u}} (step : NormalizedBlowup X)
      (tail : NormalizedBlowupSequence step.source Y) : NormalizedBlowupSequence X Y

namespace NormalizedBlowupSequence

/-- The number of normalized blowups in a finite sequence. -/
def length {X Y : Scheme.{u}} : NormalizedBlowupSequence X Y → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- The empty normalized-blowup sequence has length zero. -/
theorem length_nil (X : Scheme.{u}) : (nil X).length = 0 := sorry

/-- Prepending a normalized blowup increases the sequence length by one. -/
theorem length_cons {X Y : Scheme.{u}} (step : NormalizedBlowup X)
    (tail : NormalizedBlowupSequence step.source Y) :
    (cons step tail).length = tail.length + 1 := sorry

/-- The composite morphism from the terminal scheme of a normalized-blowup sequence to its
initial scheme. -/
noncomputable def toSource {X Y : Scheme.{u}} : NormalizedBlowupSequence X Y → (Y ⟶ X)
  | .nil _ => 𝟙 _
  | .cons step tail => tail.toSource ≫ step.hom

/-- The composite of an empty normalized-blowup sequence is the identity. -/
theorem toSource_nil (X : Scheme.{u}) : (nil X).toSource = 𝟙 X := sorry

/-- The composite of a nonempty normalized-blowup sequence is the tail composite followed by
its first normalized blowup. -/
theorem toSource_cons {X Y : Scheme.{u}} (step : NormalizedBlowup X)
    (tail : NormalizedBlowupSequence step.source Y) :
    (cons step tail).toSource = tail.toSource ≫ step.hom := sorry

/-- `EveryTargetOver s f` says that every post-initial stage of `s`, composed with `f`, is proper
over the target of `f`. -/
def EveryTargetOver {X Y S : Scheme.{u}} (s : NormalizedBlowupSequence X Y)
    (f : X ⟶ S) : Prop :=
  match s with
  | .nil _ => True
  | .cons step tail =>
      IsProper (step.hom ≫ f) ∧ tail.EveryTargetOver (step.hom ≫ f)

/-- An empty normalized-blowup sequence has no post-initial stages. -/
theorem everyTargetOver_nil {X S : Scheme.{u}} (f : X ⟶ S) :
    (nil X).EveryTargetOver f ↔ True := sorry

/-- Every post-initial stage of a nonempty sequence is proper over the base exactly when its first
target and all targets of its tail are proper over the base. -/
theorem everyTargetOver_cons {X Y S : Scheme.{u}} (step : NormalizedBlowup X)
    (tail : NormalizedBlowupSequence step.source Y) (f : X ⟶ S) :
    (cons step tail).EveryTargetOver f ↔
      IsProper (step.hom ≫ f) ∧ tail.EveryTargetOver (step.hom ≫ f) := sorry

end NormalizedBlowupSequence

/-- A two-dimensional Noetherian integral scheme has a resolution by normalized blowups when its
normalization is proper, a finite sequence of normalized point blowups has every later stage
proper over the original scheme, and its terminal scheme is regular. -/
def HasResolutionByNormalizedBlowups (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : topologicalKrullDim Y = 2) : Prop :=
  ∃ (Z : Scheme.{u}) (s : NormalizedBlowupSequence Y.normalization Z),
    IsProper Y.normalizationTo ∧
      s.EveryTargetOver Y.normalizationTo ∧ Regular Z

/-- The resolution predicate records the normalization, every proper intermediate stage, the
finite normalized-blowup chain, and its regular terminal scheme. -/
theorem hasResolutionByNormalizedBlowups_iff (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : topologicalKrullDim Y = 2) :
    HasResolutionByNormalizedBlowups Y h_dim ↔
      ∃ (Z : Scheme.{u}) (s : NormalizedBlowupSequence Y.normalization Z),
        IsProper Y.normalizationTo ∧
          s.EveryTargetOver Y.normalizationTo ∧ Regular Z := sorry

end AlgebraicGeometry.Scheme
