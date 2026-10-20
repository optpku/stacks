/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.13.3

The reusable owners live in the category-of-elements localization API.  The chapter entry keeps
only the source-facing preservation and cohomology recalls.
-/

open CategoryTheory

/- Lemma 21.13.3 (1): localization inverse image preserves injective abelian sheaves. -/
@[stacks 07A0 "(1), localization inverse image preserves injectives"]
#check @CategoryTheory.Sheaf.Localization.inverseImage_preservesInjectiveObjects

/- Lemma 21.13.3 (1), objectwise form. -/
@[stacks 07A0 "(1), inverse image of an injective abelian sheaf"]
#check @CategoryTheory.Sheaf.Localization.injective_inverseImage

/- Lemma 21.13.3 (2): cohomology over a sheaf of sets is cohomology on its localization. -/
@[stacks 07A0 "(2), cohomology comparison"]
#check @CategoryTheory.Sheaf.Localization.cohomologyOverSheaf_isomorphic

#check @CategoryTheory.Sheaf.Localization.inverseImage
#check @CategoryTheory.Sheaf.Localization.cohomology
#check @CategoryTheory.Functor.injective_obj_of_injective
