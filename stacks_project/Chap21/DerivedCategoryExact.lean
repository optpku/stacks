/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import StacksCheckRecall

@[expose] public section

/-!
# Exact functors and derived homology

The reusable comparison is owned by
`ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology`. This support file is not a
separate Chapter 21 source item; it records the exact-functor consequence of Lemma 13.16.9 and
keeps the historical objectwise entry visible to existing chapter imports.
-/

open CategoryTheory

/- Lemma 13.16.9 (015F): an exact functor commutes naturally with homology on derived
categories. -/
@[stacks 015F] #check @Functor.MapDerivedCategory.homologyFunctorIso

#check @CategoryTheory.exactFunctor_homology_iso_mapDerivedCategory

end
