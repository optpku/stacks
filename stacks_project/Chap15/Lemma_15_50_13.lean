/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.FilteredColimit.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.13

@stack 0A41
-/

@[expose] public section

/- Lemma 15.50.13: a henselian local ring is a filtered colimit of a directed system of
henselian local G-rings with local transition maps. -/
@[stacks 0A41]
#check @HenselianLocalRing.exists_filteredColimit_isGRing
