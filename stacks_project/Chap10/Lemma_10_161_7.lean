/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finite Extensions of N-1 and N-2 Domains

@stack 032K

This source-facing file recalls the shared permanence theorems for injective
module-finite maps of Noetherian domains.
-/

-- Lemma 10.161.7 (1), tag `032K`: an injective finite extension descends `N-1`.
@[stacks 032K "(1)"]
#check @IsN1Ring.of_moduleFinite

-- Lemma 10.161.7 (2), tag `032K`: an injective finite extension descends `N-2`.
@[stacks 032K "(2)"]
#check @IsN2Ring.of_moduleFinite
