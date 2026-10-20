/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.StandardOpen
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

/- Lemma 26.11.7 (1): a presheaf on the affine basis extends to a sheaf exactly when it is a
basis sheaf. -/
@[stacks 0F1A] #check AffineBasis.exists_sheaf_iff_isBasisSheaf
#check AffineBasis.extension

/- Lemma 26.11.7 (2): basis sheafness is detected by the empty open and binary standard-open
gluing. -/
@[stacks 0F1A] #check AffineBasis.isBasisSheaf_iff_standardGluing
#check AffineBasis.standardCover
#check AffineBasis.StandardGluing.emptyCondition
#check AffineBasis.StandardGluing.glueCondition
#check AffineBasis.StandardGluing.iff

end AlgebraicGeometry.Scheme
