/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Eilenberg
import StacksCheckRecall

/-!
# Lemma 15.129.1 (Eilenberg's lemma)

The Eilenberg absorption statements are recalled from their canonical ReasLib owner.

@stack 0GVF
-/

@[expose] public section

-- Lemma 15.129.1 (Eilenberg's lemma): a direct summand of a non-finitely generated free module
-- is absorbed by that free module.
@[stacks 0GVF]
#check @Module.Free.prod_equiv_self_of_prod_equiv

-- The retract form is the canonical bridge used by the projective-module corollary.
@[stacks 0GVF "retract form"]
#check @Module.Free.prod_equiv_self_of_retract
