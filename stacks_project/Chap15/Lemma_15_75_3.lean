/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ModuleResolution

import StacksCheckRecall

/-!
# Perfect modules and finite-projective resolutions

Lemma 15.75.3 identifies perfect modules with modules admitting a finite resolution by finite
projective modules.

@stack 066Q
-/

@[expose] public section

/- Lemma 15.75.3: an `R`-module is perfect if and only if it admits a resolution
`0 ⟶ F_d ⟶ ⋯ ⟶ F_0 ⟶ M ⟶ 0` with every `F_i` finite projective. -/
@[stacks 066Q "Lemma 15.75.3"]
#check @CategoryTheory.ModuleCat.isPerfect_iff_exists_finiteProjectiveResolution

#check @CategoryTheory.ModuleCat.FiniteProjective.HasResolutionLE
