/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Quasi-Finite Extensions of Japanese Domains

@stack 032I

This source file recalls the textbook formulation; the reusable declaration is
`IsN2Ring.of_quasiFinite`.
-/

-- Lemma 10.161.5, tag `032I`: an injective quasi-finite extension of a Noetherian `N-2`
-- domain is `N-2`.
@[stacks 032I]
#check @IsN2Ring.of_quasiFinite
