/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.OfZero.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison maps under standard renumbering from page zero

The composite comparison API transports entrywise isomorphisms through the page-one view and the
affine page-and-bidegree renumbering in one step.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renumbering from page zero shifts an `IsIsoFrom` comparison threshold forward by one page. -/
@[stacks 0G1Y "comparison map under renumbering from page zero", stacks 0G20]
theorem map_isIsoFrom
    {E E' : CohomologicalSpectralSequence C 0} {f : E ⟶ E'}
    {r : ℤ} (hr : 1 ≤ r)
    (h : SpectralSequence.Hom.IsIsoFrom f r (zero_le_one.trans hr)) :
    SpectralSequence.Hom.IsIsoFrom (FromZero.map f) (r + 1)
      (Renumber.two_le_pageSucc hr) := sorry

/-- A comparison that is entrywise an isomorphism from `E₁` becomes one from `E₂` after the
standard renumbering from page zero. -/
@[stacks 0G1Y "comparison from the second renumbered page", stacks 0G20]
theorem map_isIsoFrom_two
    {E E' : CohomologicalSpectralSequence C 0} {f : E ⟶ E'}
    (h : SpectralSequence.Hom.IsIsoFrom f 1 zero_le_one) :
    SpectralSequence.Hom.IsIsoFrom (FromZero.map f) 2 le_rfl := sorry

end CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero
