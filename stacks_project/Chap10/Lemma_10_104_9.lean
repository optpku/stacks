/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.CohenMacaulay.Syzygy
import StacksCheckRecall

@[expose] public section

/-!
# Maximal Cohen-Macaulay syzygies

@stack 00NG

Lemma 10.104.9 is owned by the finite-free-resolution syzygy API in ReasLib.
-/

/- Lemma 10.104.9: a finite module of depth `e` over a local Noetherian
Cohen-Macaulay ring of dimension `d` has a finite free resolution whose
`(d - e)`th syzygy is maximal Cohen-Macaulay. -/
@[stacks 00NG]
#check @ChainComplex.Syzygy.exists_maximalCohenMacaulay
