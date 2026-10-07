module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Geometric connectedness over a separably closed field

@stack 037U

Lemma 10.48.4 is the source-facing specialization of the affine geometric-connectedness owner.
The reusable statement is kept in the `SchemeOverField.GeometricallyConnected` namespace.
-/

/- Lemma 10.48.4 (Tag 037U). -/
@[stacks 037U "separably closed affine criterion"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.Spectrum.iff_connectedSpace_of_isSepClosed

end
