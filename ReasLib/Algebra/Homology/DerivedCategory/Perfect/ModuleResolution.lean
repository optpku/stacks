/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective.Resolution
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect

import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect modules and finite-projective resolutions

This leaf identifies perfect modules with modules admitting a bounded finite-projective
resolution.  The resolution itself is owned by `ModuleCat.FiniteProjective.HasResolutionLE`.

@stack 066Q
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {R : Type u} [Ring R]

/-- Lemma 15.75.3: an `R`-module is perfect if and only if it admits a finite resolution by
finite projective `R`-modules. -/
@[stacks 066Q "Lemma 15.75.3"]
theorem isPerfect_iff_exists_finiteProjectiveResolution
    (M : ModuleCat R) :
    M.IsPerfect ↔ ∃ d : ℕ, FiniteProjective.HasResolutionLE M d := sorry

end CategoryTheory.ModuleCat
