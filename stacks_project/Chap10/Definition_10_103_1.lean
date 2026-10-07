module

public import ReasLib.RingTheory.CohenMacaulay.Module
import StacksCheckRecall

@[expose] public section

/-!
Definition 10.103.1: a finite `R`-module over a Noetherian local ring is Cohen-Macaulay when
the Krull dimension of its support equals its depth.

Owner: `Module.CohenMacaulay` in `ReasLib.RingTheory.CohenMacaulay.Module`.

@stack 00N3
-/
@[stacks 00N3]
#check @Module.CohenMacaulay
