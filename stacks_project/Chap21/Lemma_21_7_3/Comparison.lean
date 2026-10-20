/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import StacksCheckRecall

/-!
The comparison support for Lemma 21.7.3 is shared infrastructure.  The canonical owners are the
`03AY` natural isomorphism for the cohomology presheaf and the derived sections-complex
calculation; this chapter directory only recalls them.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.Sheaf

@[stacks 03AY "derived sheaf inclusion as a cohomology presheaf"]
#check @cohomologyPresheafIso

@[stacks 03AY "objectwise cohomology-presheaf comparison"]
#check @CohomologyPresheaf.appIso

@[stacks 03AY "cohomology-presheaf object comparison"]
#check @CohomologyPresheaf.objIso

@[stacks 03AY "evaluated derived inclusion and sections complex"]
#check @rightDerivedInclusion_app_obj_iso_homology_sections_complex

end CategoryTheory.Sheaf
