module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Connectedness of tensor products

@stack 037R

Lemma 10.48.1 is the separably closed specialization of the reusable tensor-product
connectedness theorem.  The shared specialization keeps its source-shaped connectedness
hypotheses, while the more general owner remains available for arbitrary field extensions.
-/

/- Lemma 10.48.1 (Tag 037R). -/
@[stacks 037R "tensor-product connectedness over a separably closed field"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.TensorProduct.connectedSpace_of_isSepClosed

end
