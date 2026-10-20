/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PointBlowupSequence

/-- Every center in a finite point-blowup sequence lies over the specified subset of its
initial scheme. -/
def EveryCenterOver {X Y : Scheme.{u}} (q : PointBlowupSequence X Y) (T : Set X) : Prop :=
  match q with
  | .nil _ => True
  | .cons p f _ tail => p.1 ∈ T ∧ tail.EveryCenterOver (f ⁻¹' T)

/-- An empty point-blowup sequence has no centers. -/
theorem everyCenterOver_nil (X : Scheme.{u}) (T : Set X) :
    (nil X).EveryCenterOver T ↔ True := sorry

/-- Center support for a nonempty point-blowup sequence consists of support for its first
center and support for the remaining centers after pulling back the specified subset. -/
theorem everyCenterOver_cons {X X' Y : Scheme.{u}} (p : closedPoints X) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : PointBlowupSequence X' Y) (T : Set X) :
    (cons p f h_blowup tail).EveryCenterOver T ↔
      p.1 ∈ T ∧ tail.EveryCenterOver (f ⁻¹' T) := sorry

/-- Center support for a concatenated point-blowup sequence is equivalent to support for the
first sequence and support for the second sequence over the inverse image of the original
subset. -/
theorem everyCenterOver_append {X Y Z : Scheme.{u}} (head : PointBlowupSequence X Y)
    (tail : PointBlowupSequence Y Z) (T : Set X) :
    (head.append tail).EveryCenterOver T ↔
      head.EveryCenterOver T ∧ tail.EveryCenterOver (head.toSource ⁻¹' T) := sorry

end AlgebraicGeometry.Scheme.PointBlowupSequence
