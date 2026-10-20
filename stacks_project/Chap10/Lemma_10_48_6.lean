module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Tensor-product connected components

Lemma 10.48.6 is a recall of the two canonical atom-level owners in
`SchemeOverField.GeometricallyConnected.TensorProduct`: the map on idempotent
elements and the map on connected components.

@stack 037W
-/

/- Lemma 10.48.6 (Tag 037W) (1): the idempotent-map clause. -/
@[stacks 037W "(1)"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.TensorProduct.idempotentMap_bijective

/- Lemma 10.48.6 (Tag 037W) (2): the connected-components clause. -/
@[stacks 037W "(2)"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.TensorProduct.connectedComponentsMap_bijective

end
