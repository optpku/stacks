/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Category.ModuleCat.RingHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness after restriction of scalars

@stack 066V

If the target ring of a ring homomorphism is perfect as a module over the source, restriction of
scalars sends perfect derived objects to perfect derived objects.  The explicit target-module
presentation avoids rebuilding the regular-module equivalence in each chapter.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.75.8 (Stacks `066V`): perfectness descends along restriction of scalars when the
target module has finite perfectness over the source. -/
@[stacks 066V "perfectness after restriction of scalars"]
theorem IsPerfect.restrictScalars
    (f : R →+* S) {K : DerivedCategory (ModuleCat S)}
    (hS : ModuleCat.IsPerfect f.targetModule) (hK : K.IsPerfect) :
    DerivedCategory.IsPerfect ((ModuleCat.derivedRestrictionOfScalars f).obj K) := sorry

end CategoryTheory.DerivedCategory
