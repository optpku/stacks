/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.MaximalSubalgebra.BaseChange
import StacksCheckRecall

/-!
# Base change of maximal weakly etale subalgebras

This file records Lemma 15.106.4, Stacks `0CKU`, through the shared explicit base-change map and
its bijectivity theorem.

@stack 0CKU
-/

@[expose] public section

-- The ambient tensor map underlying the source comparison.
@[stacks 0CKU "Lemma 15.106.4, ambient map"]
#check @Subalgebra.maximalWeaklyEtale.baseChangeAmbientMap

-- Lemma 15.106.4: the canonical map into the maximal weakly etale subalgebra after base change.
@[stacks 0CKU "Lemma 15.106.4, canonical map"]
#check @Subalgebra.maximalWeaklyEtale.baseChangeMap

#check @Subalgebra.maximalWeaklyEtale.baseChangeMap_apply

-- The canonical map is an isomorphism, expressed as bijectivity of its underlying function.
@[stacks 0CKU "Lemma 15.106.4, bijectivity"]
#check @Subalgebra.maximalWeaklyEtale.baseChangeMap_bijective
