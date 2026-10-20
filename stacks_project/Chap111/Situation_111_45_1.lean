module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

@[expose] public section

universe u

open CategoryTheory.MonoidalCategory

/- Situation 111.45.1 (1): Let `k` be a field, let `X = ProjectiveSpace.scheme k n`, and
let `ℱ` be a coherent `𝒪_X`-module. Its Euler characteristic is the signed sum of
cohomology dimensions in degrees `0, …, n`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.eulerCharacteristic_eq_sum :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic
          (AlgebraicGeometry.ProjectiveSpace.toSpec k n) ℱ =
        ∑ i ∈ Finset.range (n + 1),
          ((i : ℤ).negOnePow : ℤ) *
            (AlgebraicGeometry.Scheme.Hom.cohomologyFinrank
              (AlgebraicGeometry.ProjectiveSpace.toSpec k n) ℱ i : ℤ))

/- Situation 111.45.1 (2): the Hilbert polynomial of `ℱ` is the function
`t ↦ χ(X, ℱ(t))`, owned by `ProjectiveSpace.hilbertPolynomial`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_apply :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent] (d : ℤ),
      AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k n ℱ d =
        AlgebraicGeometry.Scheme.Hom.eulerCharacteristic
          (AlgebraicGeometry.ProjectiveSpace.toSpec k n)
          (AlgebraicGeometry.ProjectiveSpace.twist k n ℱ d))

/- Situation 111.45.1 (3): `ℱ(t) = ℱ ⊗ 𝒪_X(t)`, where `𝒪_X(t)` is the `t`th twist of
the structure sheaf, as in Constructions, Definition 27.10.1. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.twist_def :
    ∀ (R : Type u) [CommRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) (d : ℤ),
      AlgebraicGeometry.ProjectiveSpace.twist R n ℱ d =
        ℱ ⊗ AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d)

/- Situation 111.45.1 (4): Varieties, Subsection 33.35.13 proves that the Hilbert
polynomial is a polynomial in `t`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_isHilbertPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      ∃ P : Polynomial ℚ, AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial k n ℱ P)
