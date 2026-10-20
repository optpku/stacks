/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.JacobiZariski.ShortComplex
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.139.1 (Tag 04B2)

The source's `moduleCatMkOfKerLERange` presentation is a source-facing
packaging of the canonical transitivity complex.  The reusable owner exposes
the maps, exactness, and smooth/formally-smooth short-exactness statements
directly.

@stack 04B2
-/

#check @KaehlerDifferential.Transitivity.map_comp_mapBaseChange
#check @KaehlerDifferential.exact_mapBaseChange_map
#check @KaehlerDifferential.Transitivity.complex
#check @KaehlerDifferential.Transitivity.exact
#check @KaehlerDifferential.Transitivity.shortExact_iff_mapBaseChange_injective
#check @KaehlerDifferential.Transitivity.shortExact_of_formallySmooth

/- Lemma 10.139.1 (Tag 04B2): smoothness of the second algebra map gives a short exact
Kähler transitivity complex. -/
@[stacks 04B2]
#check @KaehlerDifferential.Transitivity.shortExact_of_smooth
