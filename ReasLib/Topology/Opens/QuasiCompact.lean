module

public import Mathlib.CategoryTheory.Sites.Spaces
public import ReasLib.CategoryTheory.Sites.QuasiCompact

/-!
# Quasi-compact open objects

This module connects ordinary topological compactness of an open subset with the
site-theoretic quasi-compactness predicate for the canonical topology on opens.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

/-- A compact open subset is a quasi-compact object of the canonical Grothendieck site of
opens. -/
theorem quasiCompactObject_of_isCompact
    {X : Type u} [TopologicalSpace X] (U : Opens X) (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology X).QuasiCompactObject U := sorry

end TopologicalSpace.Opens
