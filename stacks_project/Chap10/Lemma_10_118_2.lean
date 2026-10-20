/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GenericFlatness.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Generic Freeness for Finitely Presented Modules

Finite-presentation generic freeness is a direct ReasLib consequence; this
file no longer depends on the preceding chapter wrapper.

@stack 051S
-/

/- Lemma 10.118.2: if `R` is a domain, `S` is finitely presented over `R`,
and `M` is finitely presented over `S`, a nonzero principal localization
makes `M` free over the localized base. -/
@[stacks 051S]
#check @GenericFlatness.exists_nonzero_away_module_free_of_finitePresentation
