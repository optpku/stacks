/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup

/-!
# Base change of almost blowup squares

This file records the stability of almost blowup squares under arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.IsAlmostBlowupSquare

/-- An almost blowup square remains an almost blowup square after base change along any
morphism. -/
theorem baseChange {X X' : Scheme.{u}} {b : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsAlmostBlowupSquare b I) {Y : Scheme.{u}} (f : Y ⟶ X) :
    IsAlmostBlowupSquare (pullback.fst f b) (I.comap f) := sorry

end AlgebraicGeometry.IsAlmostBlowupSquare
