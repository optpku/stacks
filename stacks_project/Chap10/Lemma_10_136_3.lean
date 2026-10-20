/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.BaseChange

@[expose] public section

/-!
# Syntomic Base-Change Recall

The source statement is owned by the intrinsic `RingHom.Syntomic` predicate.
The ReasLib leaf packages the tensor-product base-change formulation without
exposing the residue-field and local-complete-intersection proof plumbing.

@stack 00SN
-/

/- Lemma 10.136.3, tag 00SN: if `R → S` is syntomic and `R → R'` is any map of commutative
rings, then the canonical base-change map `R' → R' ⊗[R] S` is syntomic. -/
@[stacks 00SN "syntomic base change"]
#check @RingHom.Syntomic.baseChange
