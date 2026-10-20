/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Flatness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.128.1

@stack 00R4
-/

/- Chap10 Lemma 10 128 1 (Tag 00R4): let `R → S` be a local homomorphism of
Noetherian local rings. If `R` is a regular local ring, `S` is
Cohen--Macaulay, and `dim S = dim R + dim ((maximalIdeal R).Fiber S)`, then
`R → S` is flat.  The reusable owner has the same assumptions and conclusion. -/
@[stacks 00R4]
#check @RingHom.Flat.of_cohenMacaulay_of_fiber_dim
