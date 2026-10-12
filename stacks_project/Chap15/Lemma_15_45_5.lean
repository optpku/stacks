/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Nilradical

@[expose] public section

/-!
# Lemma 15.45.5 (0ASE)

@stack 0ASE
-/

-- Lemma 15.45.5 (1): extension of the nilradical to a henselization.
@[stacks 0ASE "Lemma 15.45.5 (1)"]
#check @IsHenselizationOf.map_nilradical

-- Lemma 15.45.5 (2): extension of the nilradical to a strict
-- henselization.
@[stacks 0ASE "Lemma 15.45.5 (2)"]
#check @IsStrictHenselizationOf.map_nilradical
