/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.MappingConeComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.14

The mapping-cone comparison is owned by the neutral degreewise-split homotopy-category leaf.  The
chapter entry retains the source label and exposes both the general fixed-endpoint bridge and the
split-monomorphic factorization specialization.
-/

namespace CochainComplex

@[stacks 014L]
#check @DegreewiseSplit.MappingCone.triangleIso
@[stacks 014L]
#check @DegreewiseSplit.MappingCone.SplitMono.triangleIso

end CochainComplex
