module

public import Mathlib.AlgebraicGeometry.QuasiAffine

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is quasi-affine if and only if its canonical morphism to the spectrum of its
global sections is a quasi-compact open immersion. -/
theorem isQuasiAffine_iff_toSpecΓ (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ QuasiCompact X.toSpecΓ ∧ IsOpenImmersion X.toSpecΓ := sorry

end AlgebraicGeometry.Scheme
