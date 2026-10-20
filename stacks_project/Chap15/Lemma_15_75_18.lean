/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.FilteredColimit
import StacksCheckRecall

/-!
# Perfect complexes over filtered colimits

Lemma 15.75.18 (0BC7) has an object-descent clause and a filtered Hom-colimit clause. The
explicit stage, comparison, and Hom-diagram data are owned by ReasLib; this chapter file is the
source-facing recall surface.

@stack 0BC7
-/

@[expose] public section

open CategoryTheory

@[stacks 0BC7 "Lemma 15.75.18"]
#check @CategoryTheory.DerivedCategory.Perfect.FilteredColimit.exists_stage_of_isPerfect

@[stacks 0BC7 "Lemma 15.75.18 (Hom colimit)"]
#check @CategoryTheory.DerivedCategory.Perfect.FilteredColimit.homDiagram_isColimit

@[stacks 0BC7 "Lemma 15.75.18 (Hom factorization)"]
#check @CategoryTheory.DerivedCategory.Perfect.FilteredColimit.exists_stage_factorization_of_isPerfect

@[stacks 0BC7 "Lemma 15.75.18 (Hom eventual equality)"]
#check @CategoryTheory.DerivedCategory.Perfect.FilteredColimit.eventually_eq_of_stage_morphisms_with_equal_colimit_images_of_isPerfect
