/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.InternalHom
import StacksCheckRecall

/-!
# Derived completion and derived internal Hom

@stack 0A6E
-/

@[expose] public section

/- Lemma 15.92.13 (1): completion of `RHom[H](K, L)` is isomorphic to
`RHom[H](K, L^∧)`. -/
@[stacks 0A6E "(1), derived completion commutes with derived internal Hom in the target"]
#check @DerivedCategory.DerivedCompletion.InternalHom.comparison
#check @DerivedCategory.DerivedCompletion.InternalHom.comparison_isIso

/- Lemma 15.92.13 (2): the unit `K ⟶ K^∧` induces an isomorphism
`RHom[H](K^∧, L^∧) ⟶ RHom[H](K, L^∧)`. -/
@[stacks 0A6E "(2), derived internal Hom inverts the completion unit in its source"]
#check @DerivedCategory.DerivedCompletion.InternalHom.unitMap
#check @DerivedCategory.DerivedCompletion.InternalHom.unitMap_isIso
