/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.Sections.Presheaf
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.26.4

The reusable presheaf-derived-sections API is owned by
`CategoryTheory.GrothendieckTopology.Derived.Sections.Presheaf`.  This chapter file is a
source-labelled recall surface only.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.Presheaf

/- Lemma 21.26.4 (0EVZ): sheafified presheaf pushout squares with a monomorphic overlap produce
functorial distinguished Mayer--Vietoris triangles for the canonical derived sections functors. -/
@[stacks 0EVZ]
#check @CategoryTheory.GrothendieckTopology.Derived.Sections.Presheaf.sheafify

@[stacks 0EVZ]
#check @CategoryTheory.GrothendieckTopology.Derived.Sections.Presheaf.sheafifyMap

@[stacks 0EVZ]
#check @freeFunctor

@[stacks 0EVZ]
#check @free

@[stacks 0EVZ]
#check @toDerived

@[stacks 0EVZ]
#check @derived

@[stacks 0EVZ]
#check @cochainRestriction

@[stacks 0EVZ]
#check @restriction

@[stacks 0EVZ]
#check @restriction_comp

@[stacks 0EVZ]
#check @toBiprod

@[stacks 0EVZ]
#check @difference

@[stacks 0EVZ]
#check @toBiprod_comp_difference

@[stacks 0EVZ]
#check @exists_triangle

end
