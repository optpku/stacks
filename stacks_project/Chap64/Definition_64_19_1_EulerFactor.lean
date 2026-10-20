module

public import ReasLib.LinearAlgebra.Determinant.EulerFactor

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

#check (LinearMap.eulerFactor : (M →ₗ[R] M) → ℕ → PowerSeries R)
