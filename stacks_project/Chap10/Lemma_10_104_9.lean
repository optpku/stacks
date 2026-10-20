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
