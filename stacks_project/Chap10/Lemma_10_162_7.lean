/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Locality
import StacksCheckRecall

@[expose] public section

/-!
# Principal-Open Locality of Nagata Conditions

@stack 032V

The reusable locality criteria are owned by ReasLib; this chapter file keeps
the source entry points.
-/

-- Lemma 10.162.7 (1), tag `032V`: a finite principal-open cover by
-- universally Japanese localizations makes the base ring universally Japanese.
@[stacks 032V "(1)"]
#check @UniversallyJapaneseRing.of_localizationAway

-- Lemma 10.162.7 (2), tag `032V`: a finite principal-open cover by Nagata
-- localizations makes the base ring Nagata.
@[stacks 032V "(2)"]
#check @NagataRing.of_localizationAway
