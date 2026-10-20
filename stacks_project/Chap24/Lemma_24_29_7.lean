/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.RightIso
public import ReasLib.CategoryTheory.MorphismProperty.IsInvertedBy
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.29.7 (tag 0FTV): the derived internal-Hom comparison is obtained in two independent
steps.  A tensor comparison supplies the left-adjoint isomorphism, and
`Adjunction.rightAdjointIsoOfLeftIso` transports it to the right-adjoint (internal-Hom) side.
`MorphismProperty.IsInvertedBy.transportIso` is the reusable denominator-inversion layer.
-/
@[stacks 0FTV] #check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso
#check @CategoryTheory.MorphismProperty.IsInvertedBy.transportIso
#check @CategoryTheory.MorphismProperty.IsInvertedBy.transportIso_hom
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_counit
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_app_counit
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_symm
