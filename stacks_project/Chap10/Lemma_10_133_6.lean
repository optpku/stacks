/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.6

@stack 09CN

Lemma 10.133.6 (Tag 09CN): for a commutative algebra `R → S` and an
`S`-module `M`, the first principal-parts sequence
`0 ⟶ Ω[S⁄R] ⊗[S] M ⟶ PrincipalParts.module R S M 1 ⟶ M ⟶ 0`
is short exact and functorial in `M`.

The reusable owner is `PrincipalParts.FirstOrder`.  It keeps the canonical
projection, cotangent map, short complex, and functorial sequence map in a
neutral algebraic namespace rather than exposing Chapter 10 implementation
names to later chapters.
-/

@[stacks 09CN]
#check @PrincipalParts.FirstOrder.projection

#check @PrincipalParts.FirstOrder.cotangentTo
#check @PrincipalParts.FirstOrder.sequence
#check @PrincipalParts.FirstOrder.sequenceMap
#check @PrincipalParts.FirstOrder.shortExact
