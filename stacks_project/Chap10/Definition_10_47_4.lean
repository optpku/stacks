/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
# Geometrically Irreducible Affine Algebras

Definition 10.47.4 is a canonical recall.  The reusable affine bridge is
owned by `AlgebraicGeometry.SchemeOverField`; this chapter file preserves the
source label while keeping the prime-spectrum formulation available to later
items.

@stack 037L
-/

/- Definition 10.47.4 (Tag 037L): `S` is geometrically irreducible over `k` when its affine
structural morphism has the canonical `GeometricallyIrreducible` property. -/
@[stacks 037L]
#check (GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))))

/- Definition 10.47.4 (Tag 037L), canonical predicate owner. -/
@[stacks 037L "geometric irreducibility predicate"]
#check @AlgebraicGeometry.GeometricallyIrreducible

/- Definition 10.47.4 (Tag 037L), affine base-change bridge. -/
@[stacks 037L]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.Spectrum.iff_baseChange
@[stacks 037L "self-geometric irreducibility"]
#check @AlgebraicGeometry.SchemeOverField.instGeometricallyIrreducible_self

end
