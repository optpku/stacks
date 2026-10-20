module

public import ReasLib.CategoryTheory.Sites.Over

import StacksCheckRecall

@[expose] public section

/-! [stacks 00Y2 (1)]
Lemma 7.27.4 (1) is the slice-site specialization of the continuous
fully-faithful sheaf-adjunction API. -/
@[stacks 00Y2 "(1)"] #check @CategoryTheory.Over.sheafAdjunctionContinuous_unit_app_isIso_of_subsingletonHom

/-! [stacks 00Y2 (2)]
Lemma 7.27.4 (2) is the corresponding cocontinuous specialization. -/
@[stacks 00Y2 "(2)"] #check @CategoryTheory.Over.sheafAdjunctionCocontinuous_counit_app_isIso_of_subsingletonHom
