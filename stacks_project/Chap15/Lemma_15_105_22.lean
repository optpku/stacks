/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.IntegralClosure
import StacksCheckRecall

/-!
# Weakly etale algebras over normal domains

This file records Lemma 15.105.22, Stacks `092W`, through the shared weakly etale integral-closure
owner.

@stack 092W
-/

@[expose] public section

-- Lemma 15.105.22: if `A` is a normal domain with fraction field `K` and `A -> B` is weakly
-- etale, then `B` is integrally closed in `B tensor[A] K`.
@[stacks 092W "Lemma 15.105.22"]
#check @Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct_fractionField
