module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.7.2 (1): affine tilde sheafification is compatible with tensor products. -/
@[stacks 01I8] #check tilde.Tensor.comparisonIsIso

/- Lemma 26.7.2 (2): affine tilde sheafification is compatible with tensor powers. -/
@[stacks 01I8] #check tilde.TensorPower.comparisonIsIso

/- Lemma 26.7.2 (3): affine tilde sheafification is compatible with symmetric powers; its
canonical comparison is invertible. -/
@[stacks 01I8] #check tilde.SymmetricPower.comparisonIsIso

/- Lemma 26.7.2 (4): affine tilde sheafification is compatible with exterior powers; its
canonical comparison is invertible. -/
@[stacks 01I8] #check tilde.ExteriorPower.comparisonIsIso

/- Lemma 26.7.2 (5): affine tilde sheafification commutes with internal Hom from a finitely
presented module; the canonical comparison is invertible. -/
@[stacks 01I8] #check tilde.InternalHom.comparisonIsIso

/- The forward comparison maps and certificate-gated inverse bridges are the lower reusable layer;
downstream callers pass an explicit `IsIso` certificate when they need inverse data. -/
#check tilde.Unit.comparison
#check tilde.Tensor.comparison
#check tilde.Tensor.comparisonInv
#check tilde.Tensor.comparisonInv_naturality
#check tilde.Tensor.comparisonIsoOf
#check tilde.Tensor.comparisonNatTrans
#check tilde.Tensor.comparisonNatTrans_app
#check tilde.TensorPower.comparison
#check tilde.TensorPower.comparisonInv
#check tilde.TensorPower.comparisonInv_naturality
#check tilde.TensorPower.comparisonIsoOf
#check tilde.TensorPower.comparisonNatTrans
#check tilde.SymmetricPower.comparison
#check tilde.SymmetricPower.comparisonInv
#check tilde.SymmetricPower.comparisonInv_naturality
#check tilde.SymmetricPower.comparisonIsoOf
#check tilde.SymmetricPower.comparisonNatTrans
#check tilde.ExteriorPower.comparison
#check tilde.ExteriorPower.comparisonInv
#check tilde.ExteriorPower.comparisonInv_naturality
#check tilde.ExteriorPower.comparisonIsoOf
#check tilde.ExteriorPower.comparisonNatTrans
#check tilde.InternalHom.comparison
#check tilde.InternalHom.comparisonInv
#check tilde.InternalHom.comparisonInv_naturality
#check tilde.InternalHom.comparisonInv_naturality_left
#check tilde.InternalHom.comparisonIsoOf
#check tilde.InternalHom.naturality
