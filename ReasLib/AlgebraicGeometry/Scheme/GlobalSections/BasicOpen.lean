module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The global-sections morphism on basic opens

This module relates the canonical morphism from a scheme to the spectrum of
its global sections to affine basic opens.
-/

@[expose] public section

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- If a basic open in a quasi-compact and quasi-separated scheme is affine, then the
restriction of the canonical global-sections morphism to the corresponding basic open of the
spectrum is an isomorphism. -/
theorem isIso_restrict_toSpecΓ_basicOpen_of_isAffineOpen
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) (hf : IsAffineOpen (X.basicOpen f)) :
    CategoryTheory.IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f) := sorry

end AlgebraicGeometry
