/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Nagata
import StacksCheckRecall

@[expose] public section

/-!
@stack 032R
# Definition 10.162.1

The two canonical ring predicates are recalled from the Normal/Nagata owner.
-/

/- Definition 10.162.1 (1): A ring is universally Japanese if every finite type `R`-algebra
that is a domain is N-2.

Definition 10.162.1 (2): A Nagata ring is a Noetherian ring whose quotient by every prime
ideal is N-2.

Owner: `UniversallyJapaneseRing`, `NagataRing` in `ReasLib.RingTheory.Normal.Nagata`. -/
@[stacks 032R "(1)"]
#check @UniversallyJapaneseRing
@[stacks 032R "(2)"]
#check @NagataRing
