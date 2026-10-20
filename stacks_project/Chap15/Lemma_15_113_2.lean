/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Ramification
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.113.2

@stack 09EB

The common branch invariants and fundamental identity are owned by
`integralClosure.Ramification`.  This source entry is a direct recall surface and introduces no
local integral-closure, fraction-field, or Galois-group instances.
-/

namespace Lemma_15_113_2

/- Lemma 15.113.2 (1): ramification indices are constant across maximal branches. -/
@[stacks 09EB "Lemma 15.113.2 (1): common ramification index"]
#check (@integralClosure.Ramification.ramificationIdx_eq_ramificationIdxIn)

/- Lemma 15.113.2 (2): inertia degrees are constant across maximal branches. -/
@[stacks 09EB "Lemma 15.113.2 (2): common inertia degree"]
#check (@integralClosure.Ramification.inertiaDeg_eq_inertiaDegIn)

/- Lemma 15.113.2 (3): the common ramification index is at least one. -/
@[stacks 09EB "Lemma 15.113.2 (3): positive ramification index"]
#check (@integralClosure.Ramification.one_le_ramificationIdxIn)

/- Lemma 15.113.2 (4): the common inertia degree is at least one. -/
@[stacks 09EB "Lemma 15.113.2 (4): positive inertia degree"]
#check (@integralClosure.Ramification.one_le_inertiaDegIn)

/- Lemma 15.113.2 (5): the degree is the number of branches times the common invariants. -/
@[stacks 09EB "Lemma 15.113.2 (5): Galois branch fundamental identity"]
#check (@integralClosure.Ramification.fundamentalIdentity)

end Lemma_15_113_2
