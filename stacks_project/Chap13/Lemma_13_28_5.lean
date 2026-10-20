module

import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.28.5

The Grothendieck-group comparison for a weak Serre subcategory is owned by
`DerivedCategory.Bounded.CohomologyIn.K0`.  The category-level degree-zero and
homology bridges live in the adjacent `Bounded.CohomologyIn` leaf.
-/

open CategoryTheory

/- Lemma 13.28.5: a weak Serre subcategory and the bounded derived category
with cohomology in it have canonically equivalent Grothendieck groups. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.K0.equiv

/- Companion check: the forward map is induced by the degree-zero embedding. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.K0.fromAbelian

/- Companion check: the inverse map is the lifted cohomological Euler characteristic. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.K0.toAbelian

/- Companion check: the degree-zero functor is a reusable category-level owner. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.Single.functor

/- Companion computations: the lifted degree-zero embedding exposes its ordinary object and map. -/
@[stacks 0FCS]
#check @DerivedCategory.Bounded.CohomologyIn.Single.functor.obj_obj

@[stacks 0FCS]
#check @DerivedCategory.Bounded.CohomologyIn.Single.functor.map_hom

/- Companion check: cohomology is lifted canonically to the weak Serre subcategory. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.Homology.functor

/- Companion check: the lifted degree-zero functor has its canonical shift sequence. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.Homology.shiftSequence

/- Companion computations: lifted bounded cohomology exposes the ordinary object and map. -/
@[stacks 0FCS]
#check @DerivedCategory.Bounded.CohomologyIn.Homology.functor.obj_obj

@[stacks 0FCS]
#check @DerivedCategory.Bounded.CohomologyIn.Homology.functor.map_hom

/- Companion check: the equivalence computes on degree-zero object classes. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.K0.equiv_apply_of

/- Companion check: its inverse computes by the lifted cohomological Euler class. -/
@[stacks 0FCS] #check @DerivedCategory.Bounded.CohomologyIn.K0.equiv_symm_apply_of
