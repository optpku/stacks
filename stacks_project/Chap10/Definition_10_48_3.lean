/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-!
# Geometrically Connected Affine Algebras

Definition 10.48.3 is a canonical recall.  The scheme-level property remains
the primary owner; its affine prime-spectrum criterion is shared through
`AlgebraicGeometry.SchemeOverField`.

@stack 037T
-/

/- Definition 10.48.3 (Tag 037T): the affine structural morphism carries mathlib's canonical
geometric-connectedness class. -/
@[stacks 037T]
#check (GeometricallyConnected (Spec.map (ofHom (algebraMap k S))))

/- Definition 10.48.3 (Tag 037T), affine base-change bridge. -/
@[stacks 037T "self-geometric connectedness"]
#check @AlgebraicGeometry.SchemeOverField.instGeometricallyConnected_self
@[stacks 037T "base-change connectedness"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyConnected.iff_connectedSpace_primeSpectrum_baseChange
@[stacks 037T "geometric predicate equivalence"]
#check @AlgebraicGeometry.GeometricallyConnected.eq_geometrically

end
