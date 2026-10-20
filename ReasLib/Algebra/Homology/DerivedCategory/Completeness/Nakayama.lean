/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-complete Nakayama vanishing

This leaf keeps the finite-generation quotient criterion independent of the chapter proof.  The
quotient is written as the canonical module quotient by `I • ⊤`, so later users can apply the
criterion without rebuilding a presentation by a list of generators.

@stack 09B9
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat.DerivedComplete

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.7 (Stacks `09B9`): a finitely generated derived-complete module whose quotient
by `I • ⊤` is zero is itself zero. -/
@[stacks 09B9 "derived-complete Nakayama vanishing"]
theorem quotient_isZero (I : Ideal A) (hI : I.FG) (M : ModuleCat A)
    (hM : M.IsDerivedCompleteWithRespectTo I)
    (hquot : IsZero (ModuleCat.of A (M ⧸ (I • (⊤ : Submodule A M))))) :
    IsZero M := sorry

end ModuleCat.DerivedComplete

end
