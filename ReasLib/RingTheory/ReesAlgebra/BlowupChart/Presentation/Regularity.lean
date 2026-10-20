module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Presentation
public import ReasLib.RingTheory.Sequence.Koszul.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# H1-regular presentations of affine blowup charts

For an H1-regular finite family, the canonical polynomial-quotient presentation
map to the affine blowup chart is bijective.

@stack 0BIQ
-/

@[expose] public section

noncomputable section

universe u

namespace AffineBlowupChart.Presentation.Tuple

variable {R : Type u} [CommRing R]

/-- Lemma 15.31.2 (Stacks tag `0BIQ`): the canonical quotient
presentation map of an H1-regular family is bijective. -/
@[stacks 0BIQ "Lemma 15.31.2"]
theorem map_bijective_of_isH1RegularSequence {r : ℕ} (f : Fin (r + 1) → R)
    (h : RingTheory.Sequence.IsH1RegularSequence f) :
    Function.Bijective (map f) := sorry

end AffineBlowupChart.Presentation.Tuple
