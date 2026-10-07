module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.NormalizedBlowupSequence

/-- Every center in a finite normalized-blowup sequence lies over the specified subset of its
initial scheme. -/
def EveryCenterOver {X Y : Scheme.{u}} (q : NormalizedBlowupSequence X Y)
    (T : Set X) : Prop :=
  match q with
  | .nil _ => True
  | .cons step tail =>
      step.point.1 ∈ T ∧ tail.EveryCenterOver (step.hom ⁻¹' T)

/-- An empty normalized-blowup sequence has no centers. -/
theorem everyCenterOver_nil (X : Scheme.{u}) (T : Set X) :
    (nil X).EveryCenterOver T ↔ True := sorry

/-- Center support for a nonempty normalized-blowup sequence consists of support for its first
center and support for the remaining centers after pulling back the specified subset. -/
theorem everyCenterOver_cons {X Y : Scheme.{u}} (step : NormalizedBlowup X)
    (tail : NormalizedBlowupSequence step.source Y) (T : Set X) :
    (cons step tail).EveryCenterOver T ↔
      step.point.1 ∈ T ∧ tail.EveryCenterOver (step.hom ⁻¹' T) := sorry

end AlgebraicGeometry.Scheme.NormalizedBlowupSequence
