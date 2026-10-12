/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Normal

@[expose] public section

/-!
# Lemma 15.45.6 (06DI)

@stack 06DI
-/

-- Lemma 15.45.6: a local ring, a henselization, and a strict
-- henselization are normal simultaneously.
@[stacks 06DI "Lemma 15.45.6"]
#check @IsHenselizationOf.isNormalRing_tfae

-- Pairwise views of the same normality comparison.
#check @IsHenselizationOf.isNormalRing_iff
#check @IsStrictHenselizationOf.isNormalRing_iff

-- Ind-etale normality ascent is the reusable core of the forward directions.
#check @RingHom.IndEtale.isNormalRing
