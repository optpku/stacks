/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.FiniteProjective
import StacksCheckRecall

/-!
# Finite projective modules over a henselian pair

The reduction functor and its henselian comparison theorems are owned by `ReasLib`; this file is
the labeled chapter recall.

@stack 0D4A
-/

@[expose] public section

/- Lemma 15.13.1 (1): reduction modulo a henselian ideal induces a bijection on isomorphism
classes of finite projective modules. -/
@[stacks 0D4A "(1), finite projective reduction is bijective on isomorphism classes"]
#check @finiteProjectiveReduction_isoClasses_bijective_of_henselianRing

/- Lemma 15.13.1 (2): every finite projective module over the quotient lifts to a finite
projective module over the henselian pair. -/
@[stacks 0D4A "(2), finite projective modules lift across henselian quotients"]
#check @exists_finiteProjective_lift_of_henselianRing

#check @finiteProjectiveReductionFunctor
#check @finiteProjective_iso_of_quotient_iso_of_henselianRing
