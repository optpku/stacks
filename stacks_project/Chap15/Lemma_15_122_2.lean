/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.UniqueFactorizationDomain.RegularLocal
import StacksCheckRecall

/-!
# Lemma 15.122.2: regular local rings are UFDs

The canonical owner is `IsRegularLocalRing.uniqueFactorizationMonoid`; this file is a
source-facing recall of the Stacks statement.

@stack 0AG0
-/

@[expose] public section

/- Lemma 15.122.2: a regular local ring is a unique-factorization monoid. -/
@[stacks 0AG0 "Lemma 15.122.2: regular local rings are UFDs"]
#check @IsRegularLocalRing.uniqueFactorizationMonoid

#check @UniqueFactorizationMonoid

end
