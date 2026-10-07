module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.NormalizedBlowupSequence

/-- `EveryStepProper s` says that every normalized-blowup morphism occurring in `s` is proper. -/
def EveryStepProper {X Y : Scheme.{u}} (s : NormalizedBlowupSequence X Y) : Prop :=
  match s with
  | .nil _ => True
  | .cons step tail => IsProper step.hom ∧ EveryStepProper tail

/-- Every step of the empty normalized-blowup sequence is proper. -/
theorem everyStepProper_nil (X : Scheme.{u}) : EveryStepProper (.nil X) ↔ True := sorry

/-- Every step of a nonempty normalized-blowup sequence is proper exactly when its first
step and every step of its tail are proper. -/
theorem everyStepProper_cons {X Y : Scheme.{u}} (step : NormalizedBlowup X)
    (tail : NormalizedBlowupSequence step.source Y) :
    EveryStepProper (.cons step tail) ↔ IsProper step.hom ∧ EveryStepProper tail := sorry

/-- `IsBaseChange s g sHat` records, stage by stage, that `sHat` is obtained from `s` by
base change along `g`. -/
inductive IsBaseChange :
    {X Y X' Y' : Scheme.{u}} → NormalizedBlowupSequence X Y → (X' ⟶ X) →
      NormalizedBlowupSequence X' Y' → Prop where
  /-- Empty normalized-blowup sequences are related along every comparison morphism. -/
  | nil {X X' : Scheme.{u}} (g : X' ⟶ X) : IsBaseChange (.nil X) g (.nil X')
  /-- Nonempty normalized-blowup sequences are related when their first-step square is
cartesian and their tails are related along the induced comparison morphism. -/
  | cons {X Y X' Y' : Scheme.{u}} (step : NormalizedBlowup X)
      (stepHat : NormalizedBlowup X') (tail : NormalizedBlowupSequence step.source Y)
      (tailHat : NormalizedBlowupSequence stepHat.source Y') (g : X' ⟶ X)
      (g₁ : stepHat.source ⟶ step.source)
      (square : IsPullback g₁ stepHat.hom step.hom g)
      (tail_isBaseChange : IsBaseChange tail g₁ tailHat) :
      IsBaseChange (.cons step tail) g (.cons stepHat tailHat)

/-- Stagewise base change preserves the length of a normalized-blowup sequence. -/
theorem IsBaseChange.length_eq {X Y X' Y' : Scheme.{u}}
    {s : NormalizedBlowupSequence X Y} {g : X' ⟶ X}
    {sHat : NormalizedBlowupSequence X' Y'} (h : IsBaseChange s g sHat) :
    s.length = sHat.length := sorry

/-- Stagewise base change supplies a cartesian square for the composite morphisms to the
initial schemes. -/
theorem IsBaseChange.exists_isPullback_toSource {X Y X' Y' : Scheme.{u}}
    {s : NormalizedBlowupSequence X Y} {g : X' ⟶ X}
    {sHat : NormalizedBlowupSequence X' Y'} (h : IsBaseChange s g sHat) :
    ∃ g₁ : Y' ⟶ Y, IsPullback g₁ sHat.toSource s.toSource g := sorry

/-- If every step of a normalized-blowup sequence is proper, then every target remains
proper over any proper base morphism. -/
theorem EveryStepProper.everyTargetOver {X Y S : Scheme.{u}}
    {s : NormalizedBlowupSequence X Y} (h : EveryStepProper s)
    (f : X ⟶ S) [IsProper f] : s.EveryTargetOver f := sorry

end AlgebraicGeometry.Scheme.NormalizedBlowupSequence
