module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.1 (0FPQ): cochain complexes of modules on a commutative ringed site carry the
canonical Koszul symmetric monoidal structure. -/
@[stacks 0FPQ]
#check @CochainComplex.Koszul.symmetricCategory

#check @CochainComplex.Koszul.braidedCategory
#check @RingedSite.CochainComplex.IntGraded.hasGoodTensor₁₂Tensor
#check @RingedSite.CochainComplex.IntGraded.hasGoodTensorTensor₂₃
