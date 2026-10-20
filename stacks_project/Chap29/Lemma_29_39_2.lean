module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.AffineSpace
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.39.2: if `π : X ⟶ S` is locally of finite type and `X` is quasi-affine, then `X`
admits an immersion over `S` into a finite-dimensional relative affine space. -/
@[stacks 04II] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.exists_immersion_to_affineSpace :
    ∀ {X S : Scheme.{u}} (π : X ⟶ S) [X.IsQuasiAffine] [LocallyOfFiniteType π],
      ∃ (n : ℕ) (i : X ⟶ 𝔸(ULift.{u} (Fin n); S)),
        IsImmersion i ∧ i ≫ (𝔸(ULift.{u} (Fin n); S) ↘ S) = π)
