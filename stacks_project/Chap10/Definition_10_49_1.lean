module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-!
# Geometrically Integral Affine Algebras

Definition 10.49.1 is a canonical recall. The shared affine criterion is
owned by `AlgebraicGeometry.SchemeOverField`.

@stack 05DX
-/

/- Definition 10.49.1 (Tag 05DX): geometrically integral affine schemes are
represented by the canonical `GeometricallyIntegral` predicate. -/
@[stacks 05DX]
#check (GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))))

/- Definition 10.49.1 (Tag 05DX), canonical predicate owner. -/
@[stacks 05DX "geometric integrality predicate"]
#check @AlgebraicGeometry.GeometricallyIntegral

/- Definition 10.49.1 (Tag 05DX), affine base-change bridge. -/
@[stacks 05DX]
#check @AlgebraicGeometry.SchemeOverField.geometricallyIntegral_iff_isDomain_tensorProduct

end
