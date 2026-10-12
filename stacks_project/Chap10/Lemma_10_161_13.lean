/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Polynomial N-1 and N-2 Domains

@stack 032O

The reusable polynomial stability results are owned by ReasLib; this chapter
file retains the textbook entry point.
-/

-- Lemma 10.161.13 (1), tag `032O`: a polynomial ring over a Noetherian
-- `N-1` domain is `N-1`.
@[stacks 032O "(1)"]
#check @IsN1Ring.polynomial

-- Lemma 10.161.13 (2), tag `032O`: a polynomial ring over a Noetherian
-- `N-2` domain is `N-2`.
@[stacks 032O "(2)"]
#check @IsN2Ring.polynomial
