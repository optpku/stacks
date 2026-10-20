/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Nagata.FormalFiber
import StacksCheckRecall

/-!
# Lemma 15.52.4

@stack 0BJ0
-/

@[expose] public section

/- Lemma 15.52.4, tag `0BJ0`: a Noetherian local ring is Nagata exactly when its formal fibers
are geometrically reduced. -/
@[stacks 0BJ0]
#check @NagataRing.iff_geometricallyReducedFormalFibers

/- The two implications are available as named API for downstream construction and elimination. -/
#check @NagataRing.geometricallyReducedFormalFibers
#check @NagataRing.of_geometricallyReducedFormalFibers
