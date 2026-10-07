module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Finite-Separable Test for Geometric Connectedness

@stack 037S

Lemma 10.48.2 is the affine `Spec` specialization of the shared scheme-level
finite-separable criterion.  The reusable owner is stated first for arbitrary
scheme morphisms over a field, with this spectrum spelling retained for affine
applications.
-/

/- Lemma 10.48.2 (Tag 037S): a `k`-algebra is geometrically connected if and only if
`Spec (R ⊗[k] K)` is connected for every finite separable field extension `K / k`. -/
@[stacks 037S "finite-separable criterion"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.Spectrum.iff_finiteSeparable
