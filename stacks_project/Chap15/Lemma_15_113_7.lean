/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.113.7

@stack 0BU5

The decomposition-group action and the conjugation map are owned by ReasLib.  The source-facing
entry checks the canonical equivariance statement directly and does not install a second action,
residue-field instance, or selected inverse.
-/

namespace Lemma_15_113_7

/- Lemma 15.113.7: the tame inertia character intertwines decomposition conjugation with the
induced action on roots of unity. -/
@[stacks 0BU5 "Lemma 15.113.7: tame inertia character conjugation"]
#check (@integralClosure.Tame.character_conj_compatible)

end Lemma_15_113_7
