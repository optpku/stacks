module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

@[expose] public section

universe u

/- Situation 111.45.1 (1): Let `k` be a field, let `X = ProjectiveSpace.scheme k n`, and
let `ℱ` be a coherent `𝒪_X`-module. The Euler characteristic `χ(X, ℱ)` is
`Scheme.Hom.eulerCharacteristic (ProjectiveSpace.toSpec k n) ℱ`. Unfolding
`eulerCharacteristic_def` recovers the signed cohomology-dimension sum; the source range
`i = 0, …, n` matches the finsum over `ℕ` because cohomology of a coherent sheaf on
projective `n`-space vanishes in degrees strictly greater than `n`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      (F : X.Modules) [F.IsCoherent], ℤ)

@[stacks 0DCE] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_def :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      (F : X.Modules) [F.IsCoherent],
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f F =
        ∑ᶠ i : ℕ,
          ((i : ℤ).negOnePow : ℤ) *
            (AlgebraicGeometry.Scheme.Hom.cohomologyFinrank f F i : ℤ))

#check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.cohomology_isZero_of_dimension_lt :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent]
      (i : ℕ), n < i →
      CategoryTheory.Limits.IsZero
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n) ℱ i))

/- Situation 111.45.1 (2): the Hilbert polynomial of `ℱ` is the function
`t ↦ χ(X, ℱ(t))`, owned by `ProjectiveSpace.hilbertPolynomial`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      ℤ → ℤ)

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
  (AlgebraicGeometry.ProjectiveSpace.twist :
    ∀ (R : Type u) [CommRing R] (n : ℕ),
      (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules →
        ℤ → (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules)

@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf :
    ∀ (R : Type u) [CommRing R] (n : ℕ),
      ℤ → (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules)

/- Situation 111.45.1 (4): Varieties, Subsection 33.35.13 proves that the Hilbert
polynomial is a polynomial in `t`. -/
@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_isNumericalPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      IsNumericalPolynomial
        (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k n ℱ))

@[stacks 0DCE] #check
  (AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      Polynomial ℚ → Prop)
