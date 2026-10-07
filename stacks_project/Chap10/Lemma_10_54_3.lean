module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import ReasLib.RingTheory.EssentialFiniteness.RingHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.54.3

@stack 0AUF
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Import rationale: the essentially-finite-type predicate and its base-change stability are
provided by Mathlib, while the essentially-finite-presentation companion is owned by the ReasLib
ring-hom leaf. Keeping both imports explicit avoids routing this recall through Lemma 10.54.2. -/

/- Companion recall: the essentially finite type base-change statement is the canonical mathlib
theorem `RingHom.EssFiniteType.isStableUnderBaseChange`. -/
#check @RingHom.EssFiniteType.isStableUnderBaseChange

/- Lemma 10.54.3: essential finite presentation is stable under base change. In the chapter's
owner namespace, this is exactly `RingHom.EssFinitePresentation.isStableUnderBaseChange`. -/
@[stacks 0AUF]
#check @RingHom.EssFinitePresentation.isStableUnderBaseChange
