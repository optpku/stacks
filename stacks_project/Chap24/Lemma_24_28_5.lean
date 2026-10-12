/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Naturality
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.28.5 (tag 0FTJ): in the derived-pullback situation, a morphism
`N ⟶ N'` which is an isomorphism on cohomology sheaves induces an isomorphism
between the left derived tensor functors with right factors `N` and `N'`.

The reusable algebraic DG owner constructs the natural transformation from the bimodule map
and proves it invertible from the quasi-isomorphism hypothesis.  The corresponding sheaf-DG
tensor functor is not yet implemented; this check records the exact reusable tensor API rather
than weakening the conclusion to a generic underived natural isomorphism.
-/
@[stacks 0FTJ "quasi-isomorphic bimodules induce isomorphic derived tensor functors"]
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_isIso_of_quasiIso
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_fac
#check @DifferentialGradedBimodule.Tensor.derivedNatIso
