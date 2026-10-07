module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness under derived extension of scalars

@stack 066W

Derived extension of scalars sends perfect objects to perfect objects.  The explicit ring-map
form is the reusable owner; chapter-specific `algebraMap` notation belongs only in a thin facade.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.75.9 (Stacks `066W`): derived extension of scalars preserves perfect objects. -/
@[stacks 066W "perfectness after derived extension of scalars"]
theorem IsPerfect.extension
    (f : R →+* S) {K : DerivedCategory (ModuleCat R)} (hK : K.IsPerfect) :
    DerivedCategory.IsPerfect ((ModuleCat.derivedExtensionOfScalars f).obj K) := sorry

end CategoryTheory.DerivedCategory
