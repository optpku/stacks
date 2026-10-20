module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint
import StacksCheckRecall

/-!
# Field-valued morphisms into standard projective space

The identification of the slice Hom set `Mor_{Spec R}(Spec k, P^n_R)` with
`ℙ k (Fin (n + 1) → k)`, the nonzero coordinate tuples modulo unit scaling.
For the identity base map, `fieldPoint` gives the morphism `Spec k ⟶ P^n_k`
denoted by homogeneous coordinates `(x₀ : … : xₙ)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

universe u

/- Exercise 111.39.1: for every ring map `φ : R →+* k` to a field and `n : ℕ`,
nonzero coordinate tuples modulo unit scaling classify the morphisms over `Spec R`.
For the identity base map, `fieldPoint` is the morphism denoted `(x₀ : … : xₙ)`. -/
@[stacks 02A7] #check (AlgebraicGeometry.ProjectiveSpace.homMk_bijective :
  ∀ {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ),
    Function.Bijective (AlgebraicGeometry.ProjectiveSpace.homMk φ n))
