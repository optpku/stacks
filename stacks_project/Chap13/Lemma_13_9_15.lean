/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.HomotopyReplacement
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.15

The finite split-monomorphic homotopy replacement now lives in the neutral ReasLib leaf
`CochainComplex.HomotopyReplacement`.  Its induction infrastructure is split into the generic
`ComposableArrows` snoc construction, the associated morphism/naturality API, and the
shape-independent termwise split morphism property.
-/

namespace CategoryTheory
namespace ComposableArrows

@[stacks 014M]
#check @snocObj
@[stacks 014M]
#check @snocOldMap
@[stacks 014M]
#check @snocLastMap
@[stacks 014M]
#check @snoc
@[stacks 014M]
#check @snoc_obj_castSucc
@[stacks 014M]
#check @snoc_obj_last
@[stacks 014M]
#check @snoc_map_castSucc
@[stacks 014M]
#check @snoc_map_last

@[stacks 014M]
#check @snocComponents
@[stacks 014M]
#check @snocComponents_naturality
@[stacks 014M]
#check @snocHom
@[stacks 014M]
#check @snocHom_app_castSucc
@[stacks 014M]
#check @snocHom_app_last

@[stacks 014M]
#check @arrowProperty
@[stacks 014M]
#check @objectProperty
@[stacks 014M]
#check @componentProperty
@[stacks 014M]
#check @HomologicalComplex.termwiseSplitMono

@[stacks 014M]
#check @SplitMonoReplacement
@[stacks 014M]
#check @SplitMonoReplacement.nonempty
@[stacks 014M]
#check @exists_splitMonoReplacement
@[stacks 014M]
#check @exists_splitMono_homotopyReplacement

end ComposableArrows
end CategoryTheory
