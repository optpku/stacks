/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.131.4

@stack 00RP
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.131.4: if the structure map `R → S` is surjective, then the module of Kähler
differentials `Ω[S⁄R]` is zero. In Lean, a module being zero is expressed as
`Subsingleton Ω[S⁄R]`, and this is exactly the canonical theorem
`KaehlerDifferential.subsingleton_of_surjective`. -/
@[stacks 00RP "vanishing Kähler differentials for surjections"]
#check @KaehlerDifferential.subsingleton_of_surjective
