module

public import ReasLib.RingTheory.FittingIdeal.LocallyFree
import StacksCheckRecall

@[expose] public section

universe u v w

open scoped FittingIdeal

/- Exercise 111.25.1 (1): let `R` be a commutative ring and `M` a finite `R`-module. A
presentation `⨁_{j ∈ J} R ⟶ R^{⊕ n} ⟶ M ⟶ 0` is given by generators
`x₁, …, xₙ` of `M` (the images of the standard basis under a surjection
`π : (Fin n → R) →ₗ[R] M`) and an `n × J` matrix `A` whose columns generate
`LinearMap.ker π`. The ideal of `(n - k) × (n - k)` minors of `A` is
independent of the presentation, and is the `k`th Fitting ideal
`Fit[R]_(k)(M)`. -/
@[stacks 02E1]
#check (fittingIdeal_eq_minorIdeal_of_span_eq_ker :
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (k : ℕ) {n : ℕ} {J : Type w} (π : (Fin n → R) →ₗ[R] M),
    Function.Surjective π → ∀ (A : Matrix (Fin n) J R),
    Submodule.span R (Set.range (fun j => fun i => A i j)) = LinearMap.ker π →
    fittingIdeal R M k = Matrix.minorIdeal (n - k) A)

#check (presentationFittingIdeal :
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (_ : ℕ) {n : ℕ}, ((Fin n → R) →ₗ[R] M) → Ideal R)

#check (presentationFittingIdeal_eq_of_surjective :
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {n n' k : ℕ} (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M),
    Function.Surjective π → Function.Surjective π' →
    presentationFittingIdeal R M k π = presentationFittingIdeal R M k π')

#check (fittingIdeal :
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ℕ → Ideal R)

#check (fittingIdeal_eq_presentationFittingIdeal :
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (k : ℕ) {n : ℕ} (π : (Fin n → R) →ₗ[R] M),
    Function.Surjective π → Fit[R]_(k)(M) = presentationFittingIdeal R M k π)

/- Exercise 111.25.1 (2): Fitting ideals are nested:
`Fit[R]_(0)(M) ≤ Fit[R]_(1)(M) ≤ Fit[R]_(2)(M) ≤ ⋯`. -/
@[stacks 02E1]
#check (FittingIdeal.monotone :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {k l : ℕ}, k ≤ l → Fit[R]_(k)(M) ≤ Fit[R]_(l)(M))

/- Exercise 111.25.1 (3): `M` is locally free of rank `r` if and only if
`Fit_{r - 1}(M) = 0` and `Fit_r(M) = R`, with the case `r = 0` using
`precedingFittingIdeal R M 0 = ⊥`, not truncated natural subtraction. -/
@[stacks 02E1]
#check (FittingIdeal.finiteLocallyFreeOfRank_tfae :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (r : ℕ),
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M r
      , precedingFittingIdeal R M r = ⊥ ∧ Fit[R]_(r)(M) = ⊤
      , (∀ k, k < r → Fit[R]_(k)(M) = ⊥) ∧ ∀ k, r ≤ k → Fit[R]_(k)(M) = ⊤
      ])
