/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.10.5

The right-derived sheaf-to-presheaf comparison is owned by the explicit
`Sheaf.CohomologyPresheaf` natural isomorphism API.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

section LeftExact

universe u v

variable {C : Type u} [Category.{max u v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max u v}]

#synth PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{max u v})

end LeftExact

@[stacks 03AY "derived sheaf inclusion as a cohomology presheaf"]
#check @cohomologyPresheafIso

@[stacks 03AY "derived sheaf inclusion comparison"]
#check @cohomologyPresheafComparison

@[stacks 03AY "objectwise derived sheaf inclusion comparison"]
#check @CohomologyPresheaf.objIso

@[stacks 03AY "evaluated derived sheaf inclusion comparison"]
#check @CohomologyPresheaf.appIso
