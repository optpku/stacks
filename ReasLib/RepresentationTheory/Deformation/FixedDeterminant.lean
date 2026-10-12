/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RepresentationTheory.Deformation.Local

@[expose] public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup IsLocalRing

universe u v w

namespace Deformation

/-- The coefficient character reduces to the determinant of the residual representation. -/
def LiftsResidualDeterminant {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (δ : G →ₜ* ℤ_[ℓ]ˣ) : Prop :=
  (Units.map PadicInt.toZMod.toMonoidHom).comp δ.toMonoidHom =
    GeneralLinearGroup.det.comp ρ₀.toMonoidHom

/-- A representation has the chosen determinant after extending coefficients. -/
def HasFixedDeterminant {ℓ : ℕ} [Fact ℓ.Prime] {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [Algebra ℤ_[ℓ] R] [TopologicalSpace R]
    (δ : G →ₜ* ℤ_[ℓ]ˣ) (ρ : G →ₜ* GL n R) : Prop :=
  ∀ g : G, (ρ g).det = Units.map (algebraMap ℤ_[ℓ] R).toMonoidHom (δ g)

/-- A residual lift has the prescribed determinant and reduces to the residual representation. -/
def IsFixedDeterminantDeformation {ℓ : ℕ} [Fact ℓ.Prime]
    {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (δ : G →ₜ* ℤ_[ℓ]ˣ)
    (ρ : G →ₜ* GL n R) : Prop :=
  LiftsResidualDeterminant ρ₀ δ ∧ IsDeformation ρ₀ ρ ∧ HasFixedDeterminant δ ρ

/-- Universality among complete local deformations with one fixed determinant, using the same determinant in every test algebra. -/
def IsUniversalFixedDeterminantDeformation {ℓ : ℕ} [Fact ℓ.Prime]
    {n : Type v} {G : Type w} {R : Type u}
    [DecidableEq n] [Fintype n] [Group G] [TopologicalSpace G]
    [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (ρ₀ : G →ₜ* GL n (ZMod ℓ)) (δ : G →ₜ* ℤ_[ℓ]ˣ)
    (ρuniv : G →ₜ* GL n R) : Prop :=
  IsFixedDeterminantDeformation ρ₀ δ ρuniv ∧
    ∀ (S : Type u) [CommRing S] [IsLocalRing S] [Algebra ℤ_[ℓ] S]
      [TopologicalSpace S] [IsTopologicalRing S]
      [Fact (IsAdic (maximalIdeal S))]
      [IsAdicComplete (maximalIdeal S) S] [IsLAdicAlgebra ℓ S]
      (σ : G →ₜ* GL n S),
      IsFixedDeterminantDeformation ρ₀ δ σ →
        ∃! ψ : R →ₐ[ℤ_[ℓ]] S,
          IsLocalHom ψ.toRingHom ∧
            IsConjugate ((GeneralLinearGroup.map ψ.toRingHom).comp ρuniv.toMonoidHom)
              σ.toMonoidHom

end Deformation
