/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.OfZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison maps after forgetting the zeroth page

The page-one view preserves entrywise isomorphisms from every positive page onward.  This is the
comparison-property analogue of the categorical `IsIso` instance in `PositivePage.IsIso`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SpectralSequence.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-- Forgetting the zeroth page preserves entrywise isomorphisms from a positive page onward. -/
@[stacks 0BDU "comparison map after forgetting the zeroth page"]
theorem map_isIsoFrom
    {E E' : SpectralSequence C c 0} {f : E ⟶ E'}
    {r : ℤ} (hr : 1 ≤ r)
    (h : SpectralSequence.Hom.IsIsoFrom f r (zero_le_one.trans hr)) :
    SpectralSequence.Hom.IsIsoFrom (map f) r hr := sorry

end CategoryTheory.SpectralSequence.Page.One
