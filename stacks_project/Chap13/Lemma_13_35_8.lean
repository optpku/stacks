module

import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing.Extension
import StacksCheckRecall

@[expose] public section

/-!
# Additive Extension Stages and Homological Amplitude

The reusable interval and closure API for this item is owned by ReasLib.  The
exact bound below is stronger and is the preferred downstream interface.
-/

/- Lemma 13.35.8 (Stacks 0FX8), canonical strengthened form: every additive extension stage
preserves the translated vanishing interval of its generators. -/
@[stacks 0FX8]
#check @CategoryTheory.Functor.shiftVanishingIn.additiveExtensionStage_le

/- Lemma 13.35.8 (Stacks 0FX8), endpoint-multiple form.  The normalization `a ≤ 0 ≤ b`
is necessary for the displayed interval to contain the exact stage bound; it is not implied by
the source's weaker assumption `a ≤ b`. -/
@[stacks 0FX8]
#check @CategoryTheory.Functor.shiftVanishingIn.additiveExtensionStage_symmetric_le
