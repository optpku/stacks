module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.DeRhamCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 50.11.4: for `i ≤ n`, the degree-`2 * i` de Rham cohomology of
standard projective `n`-space over `A` has the `i`th de Rham Chern power of `𝒪(1)`
as its singleton basis. -/
@[stacks 0FMJ]
#check (AlgebraicGeometry.ProjectiveSpace.deRhamChernPower_basis :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n)
      (C : Scheme.DeRham.ChernClassContext (ProjectiveSpace.toSpec A n))
      (i : ℕ) (hi : i ≤ n),
      ∃ b : Module.Basis (Fin 1) A
          (Scheme.DeRham.cohomologyOverAffineBase (ProjectiveSpace.toSpec A n)
            (2 * (i : ℤ))),
        b 0 = ProjectiveSpace.deRhamChernPower A n C i)

/- Lemma 50.11.4: the de Rham cohomology of standard projective `n`-space over
`A` vanishes in every integer degree outside `2 * i` for `i ≤ n`. -/
@[stacks 0FMJ]
#check (AlgebraicGeometry.ProjectiveSpace.deRhamCohomology_isZero :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (q : ℤ)
      (hq : ¬ ∃ i : ℕ, i ≤ n ∧ q = 2 * (i : ℤ)),
      IsZero (Scheme.DeRham.cohomologyOverAffineBase (ProjectiveSpace.toSpec A n) q))

#check AlgebraicGeometry.ProjectiveSpace.deRhamChernPower
