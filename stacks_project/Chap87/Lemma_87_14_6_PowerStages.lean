module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages

/-!
# Compatibility view of the affine power stages

The reusable power-stage API is owned by `ReasLib`; this source-side module
keeps the historical import path for existing chapter consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.powerStage :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A],
    (Spec (.of A) ⟶ S) → Ideal A → ℕ → Over S)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
