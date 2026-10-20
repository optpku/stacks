/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.2

This file recalls the canonical torsion properties of the double-dual evaluation map.

@stack 0AV0
-/

@[expose] public section

/- Lemma 15.23.2 (1): a reflexive module over a domain is torsion-free. -/
@[stacks 0AV0 "Lemma 15.23.2 (1)"]
#check @Module.IsReflexive.to_isTorsionFree

/- Lemma 15.23.2 (2), kernel clause: for a finite module over a domain, the kernel of the
double-dual evaluation map is torsion. -/
@[stacks 0AV0 "Lemma 15.23.2 (2), kernel clause"]
#check @Module.Dual.eval_ker_isTorsion

/- Lemma 15.23.2 (2), cokernel clause: for a finite module over a domain, the cokernel of the
double-dual evaluation map is torsion. -/
@[stacks 0AV0 "Lemma 15.23.2 (2), cokernel clause"]
#check @Module.Dual.eval_cokernel_isTorsion

/- Lemma 15.23.2 (3): for a finite module over a domain, the double-dual evaluation map is
injective exactly when the module is torsion-free. -/
@[stacks 0AV0 "Lemma 15.23.2 (3)"]
#check @Module.Dual.eval_injective_iff_isTorsionFree
