/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness
import StacksCheckRecall

@[expose] public section

/-!
# Essentially Finite-Type Universally Japanese Algebras

@stack 032S

The reusable ring-level permanence result is owned by ReasLib; this source
file records the textbook entry point.
-/

-- Lemma 10.162.4, tag `032S`: an essentially finite-type algebra over a
-- universally Japanese ring is universally Japanese.
@[stacks 032S]
#check @UniversallyJapaneseRing.of_essFiniteType
