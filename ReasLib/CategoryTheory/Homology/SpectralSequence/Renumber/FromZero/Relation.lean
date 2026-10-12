/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded.FromZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard renumberings of zero-based spectral sequences

This file names the relation between a zero-based cohomological spectral sequence and any
`E₂`-sequence isomorphic to its standard page-and-bidegree renumbering.  Keeping this relation
beside `fromZero` lets convergence and realization APIs retain the original sequence without
repeating the intermediate page-one view.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An `E₂`-spectral sequence is a standard renumbering from `E₀` when it is isomorphic to the
page-and-bidegree renumbering obtained after forgetting the zeroth page. -/
@[stacks 0G1Y "renumbering relation from page zero", stacks 0G20]
def IsFromZero (E : CohomologicalSpectralSequence C 0)
    (E' : E₂CohomologicalSpectralSequence C) : Prop :=
  CohomologicalSpectralSequence.IsRenumbering (SpectralSequence.Page.One.ofZero E) E'

/-- The named relation is equivalent to the underlying page-one renumbering relation. -/
@[simp, stacks 0G1Y "characterization of renumbering from page zero", stacks 0G20]
theorem isFromZero_iff (E : CohomologicalSpectralSequence C 0)
    (E' : E₂CohomologicalSpectralSequence C) :
    IsFromZero E E' ↔
      CohomologicalSpectralSequence.IsRenumbering
        (SpectralSequence.Page.One.ofZero E) E' := sorry

/-- The canonical standard renumbering is a renumbering from page zero. -/
@[stacks 0G1Y "canonical renumbering from page zero", stacks 0G20]
theorem isFromZero_fromZero (E : CohomologicalSpectralSequence C 0) :
    IsFromZero E (fromZero E) := sorry

namespace IsFromZero

/-- A renumbering from page zero identifies every new page with the restricted preceding page. -/
@[stacks 0G1Y "page comparison for renumbering from page zero", stacks 0G20]
theorem pageIso {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsFromZero E E')
    (r : ℤ) (hr : 2 ≤ r) :
    Nonempty
      (E'.page r hr ≅
        page (SpectralSequence.Page.One.ofZero E) r hr) := sorry

/-- Entrywise form of the standard renumbering formula from a zero-based sequence. -/
@[stacks 0G1Y "entry comparison for renumbering from page zero", stacks 0G20]
theorem entryIso {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsFromZero E E')
    (r : ℤ) (hr : 2 ≤ r) (i j : ℤ) :
    Nonempty
      ((E'.page r hr).X (i, j) ≅
        (E.page (r - 1) (zero_le_one.trans (one_le_priorPage r hr))).X
          (-j, i + 2 * j)) := sorry

/-- Standard renumbering from page zero preserves boundedness. -/
@[stacks 0G1Y "boundedness under renumbering from page zero", stacks 0G20]
theorem isBounded_iff {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsFromZero E E') :
    E'.IsBounded ↔ CohomologicalSpectralSequence.IsBoundedFromZero E := sorry

/-- A bounded page-one view gives a bounded renumbering from page zero. -/
@[stacks 0G1Y "bounded renumbering from page zero", stacks 0G20]
theorem isBounded {E : CohomologicalSpectralSequence C 0}
    {E' : E₂CohomologicalSpectralSequence C} (h : IsFromZero E E')
    (hE : CohomologicalSpectralSequence.IsBoundedFromZero E) : E'.IsBounded := sorry

end IsFromZero

end CategoryTheory.CohomologicalSpectralSequence.Renumber
