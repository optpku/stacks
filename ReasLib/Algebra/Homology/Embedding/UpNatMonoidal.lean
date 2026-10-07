module

public import ReasLib.Algebra.Homology.ComplexShapeSigns.Nat
public import ReasLib.Algebra.Homology.Embedding.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Monoidal support for the nonnegative-to-integer embedding

The Cech row complex is indexed by `ℕ`, while the total complex uses `ℤ`.  This leaf registers
the canonical additivity and tensor-sign facts for `ComplexShape.embeddingUpNat`, so the generic
extension-by-zero tensor comparison can be used without proof-local instances.
-/

@[expose] public section

namespace ComplexShape.embeddingUpNat

/-- 20.25.3.2 (07MB): the standard embedding from nonnegative to integer cochain degrees is additive. -/
@[stacks 07MB "additivity of the nonnegative-to-integer cochain embedding"]
instance isAdditive :
    ComplexShape.Embedding.IsAdditive ComplexShape.embeddingUpNat := sorry

/-- 20.25.3.2 (07MB): the standard embedding preserves cochain tensor signs. -/
@[stacks 07MB "tensor signs for the nonnegative-to-integer cochain embedding"]
instance preservesTensorSigns :
    ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingUpNat := sorry

#synth ComplexShape.Embedding.IsAdditive ComplexShape.embeddingUpNat
#synth ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingUpNat

end ComplexShape.embeddingUpNat

end
