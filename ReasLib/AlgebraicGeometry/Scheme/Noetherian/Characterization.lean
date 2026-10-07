module

public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme is locally Noetherian exactly when each point has an affine open neighbourhood
whose ring of sections is Noetherian. -/
theorem isLocallyNoetherian_iff_affineOpen_neighborhoods (X : Scheme.{u}) :
    IsLocallyNoetherian X ↔ ∀ point : X, ∃ neighborhood : X.affineOpens,
      point ∈ (neighborhood : X.Opens) ∧ IsNoetherianRing Γ(X, neighborhood) := sorry

/-- A scheme is Noetherian exactly when it is compact and its rings of sections on all affine
opens are Noetherian. -/
theorem isNoetherian_iff_compactSpace_and_affineSections (X : Scheme.{u}) :
    IsNoetherian X ↔ CompactSpace X ∧ ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U) := sorry

end AlgebraicGeometry
