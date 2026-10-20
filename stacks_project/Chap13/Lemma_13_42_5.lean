/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Pro.Sequential.Homology.Isomorphism
import StacksCheckRecall

@[expose] public section

/- Lemma 13.42.5: a morphism of uniformly bounded sequential derived towers is a
pro-isomorphism when it is a pro-isomorphism on cohomology in every degree of the common
bounding interval. -/
@[stacks 0G3D] #check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.toHom_isIso

#check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.toHom_isIso_iff
#check @CategoryTheory.Pro.SequentialHom.toHom_map_ofNatTrans
#check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.quotientToHom_isIso
#check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.hasRepresentativeInverse
#check @CategoryTheory.Pro.SequentialHom.HasRepresentativeInverse.targetTransition_factors
#check @CategoryTheory.Pro.SequentialHom.HasRepresentativeInverse.sourceTransition_factors
