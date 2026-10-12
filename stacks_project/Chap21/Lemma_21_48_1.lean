/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.1 (0FPQ): cochain complexes of modules on a commutative ringed site carry the
canonical Koszul symmetric monoidal structure. -/
@[stacks 0FPQ]
#check @CochainComplex.Koszul.symmetricCategory

#check @CochainComplex.Koszul.braidedCategory
#check @RingedSite.CochainComplex.IntGraded.hasGoodTensor₁₂Tensor
#check @RingedSite.CochainComplex.IntGraded.hasGoodTensorTensor₂₃
