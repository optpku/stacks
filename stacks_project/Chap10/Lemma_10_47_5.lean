module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.IrreducibleCriteria
import StacksCheckRecall

@[expose] public section

/-!
# Geometric Irreducibility over a Separably Closed Field

Lemma 10.47.5 is the separably-closed specialization of the reusable affine
criterion.  The shared statement is formulated with `PrimeSpectrum R`, the
canonical ring model of `Spec R`.

@stack 037M
-/

/- Lemma 10.47.5 (Tag 037M): over a separably closed field, an affine algebra
is geometrically irreducible exactly when its prime spectrum is irreducible. -/
@[stacks 037M]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_of_isSepClosed
