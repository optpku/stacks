/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
import StacksCheckRecall

/-!
# Principal ideal domains are Dedekind domains

@stack 0AUQ
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- Lemma 10.120.15 (Stacks `0AUQ`): a principal ideal domain has Mathlib's canonical
Dedekind-domain instance. -/
@[stacks 0AUQ]
#check (IsPrincipalIdealRing.isDedekindDomain R : IsDedekindDomain R)
