module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineSpace

/-- An affine scheme with an étale morphism to affine space over a positive-characteristic
field admits a finite étale morphism to the same affine space over that field. -/
theorem existsFiniteEtaleHom
    {k : Type u} [Field k] (p n : ℕ) [CharP k p] (h_positiveChar : 0 < p)
    {X : Scheme.{u}}
    (f : X ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))) [IsAffine X] [Etale f] :
    ∃ g : X ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)),
      (IsFinite g ∧ Etale g) ∧
        g ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)) ↘ Spec (CommRingCat.of.{u} k)) =
          f ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)) ↘ Spec (CommRingCat.of.{u} k)) := sorry

end AlgebraicGeometry.AffineSpace
