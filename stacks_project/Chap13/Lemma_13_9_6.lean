/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitMonoFactorization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.6

The split-monomorphic mapping-cone factorization is owned by the neutral ReasLib leaf, whose
atomic APIs are accompanied by the source-compatible bridge recalled below.
-/

namespace CochainComplex

@[stacks 013N]
#check @SplitMonoFactorization.factorization

end CochainComplex
