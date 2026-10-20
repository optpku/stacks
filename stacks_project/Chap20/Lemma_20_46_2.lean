/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect.MappingCone
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 20.46.2

The statement is the arbitrary-site specialization of the generic mapping-cone theorem for
bounded complexes satisfying a coproduct-closed termwise object property.
-/

/- Lemma 20.46.2 (08C5): the cone of a morphism between strictly perfect complexes is strictly
perfect. -/
@[stacks 08C5] #check @SheafOfModules.CochainComplex.IsStrictlyPerfect.mappingCone

#check @CochainComplex.boundedTermsIn_mappingCone
#check @SheafOfModules.CochainComplex.IsTermwiseFiniteFreeRetract.mappingCone

end
