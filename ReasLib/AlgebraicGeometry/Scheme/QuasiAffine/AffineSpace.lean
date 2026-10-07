module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.AffineSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-- Any quasi-affine scheme admits an affine scheme over it whose pullback to every affine scheme
over it is a fixed finite-dimensional relative affine space. -/
theorem exists_affineSpacePullback {X : Scheme.{u}} (hX : X.IsQuasiAffine) :
    ∃ (n : ℕ) (T : Scheme.{u}) (π : T ⟶ X),
      IsAffine T ∧
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X), IsAffine X' →
        Nonempty (Over.mk (pullback.snd π f) ≅
          Over.mk (𝔸(ULift.{u} (Fin n); X') ↘ X')) := sorry

/-- A locally finite type morphism from a quasi-affine scheme factors through an immersion into
a finite-dimensional relative affine space. -/
theorem exists_immersion_to_affineSpace {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsQuasiAffine] [LocallyOfFiniteType π] :
    ∃ (n : ℕ) (i : X ⟶ 𝔸(ULift.{u} (Fin n); S)),
      IsImmersion i ∧ i ≫ (𝔸(ULift.{u} (Fin n); S) ↘ S) = π := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
