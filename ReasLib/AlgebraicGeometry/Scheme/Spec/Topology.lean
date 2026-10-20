/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Topological Bridges for Affine Spectra

This leaf records the topological identifications between the scheme `Spec R`
and the ring-theoretic space `PrimeSpectrum R`.  It deliberately exposes
property-level bridges instead of making downstream proofs unfold the
implementation of the affine scheme.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry

section

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The affine scheme `Spec R` is irreducible exactly when the usual prime
spectrum of `R` is irreducible. -/
@[stacks 00I7 "affine spectrum irreducibility bridge"]
theorem irreducibleSpace_spec_iff_irreducibleSpace_primeSpectrum :
    IrreducibleSpace (Spec (of R)) ↔ IrreducibleSpace (PrimeSpectrum R) := sorry

/-- The scheme map induced by a ring homomorphism is open exactly when its map
on prime spectra is open. -/
@[stacks 00I7 "affine spectrum open-map bridge"]
theorem isOpenMap_specMap_iff_isOpenMap_primeSpectrum_comap (f : R →+* S) :
    IsOpenMap (Spec.map (ofHom f)) ↔ IsOpenMap (PrimeSpectrum.comap f) := sorry

end

end AlgebraicGeometry
