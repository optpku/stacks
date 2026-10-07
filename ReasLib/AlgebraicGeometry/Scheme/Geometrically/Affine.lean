module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine Geometric Properties Over a Field

This leaf is the shared affine bridge between scheme-theoretic geometric
properties and the usual ring presentations after a field base change.  All
three bridges use the same `Spec.map` owner and the same tensor orientation,
so downstream arguments can move between geometric and ring language without
reconstructing a pullback isomorphism or introducing a chapter-local theorem.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SchemeOverField

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- An affine `k`-algebra is geometrically irreducible exactly when every prime spectrum
obtained by extension to a field over `k` is irreducible. -/
@[stacks 037L]
theorem GeometricallyIrreducible.Spectrum.iff_baseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) := sorry

/-- The ground field is geometrically irreducible over itself. -/
@[stacks 037L]
instance instGeometricallyIrreducible_self :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k k))) := sorry

/-- The ground field is geometrically connected over itself. -/
@[stacks 037T]
instance instGeometricallyConnected_self :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k k))) := sorry

/-- An affine `k`-algebra is geometrically connected exactly when every prime spectrum
obtained by extension to a field over `k` is connected. -/
@[stacks 037T]
theorem GeometricallyConnected.iff_connectedSpace_primeSpectrum_baseChange :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (PrimeSpectrum (S ⊗[k] K)) := sorry

/-- An affine `k`-algebra is geometrically integral exactly when every extension to a field
over `k` is a domain. -/
@[stacks 05DX]
theorem geometricallyIntegral_iff_isDomain_tensorProduct :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (S ⊗[k] K) := sorry

end

end AlgebraicGeometry.SchemeOverField
