module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.End.Nilpotent

/-!
# Nilpotent Perturbations of Multivariate Polynomial Endomorphisms

This leaf turns the general module-endomorphism criterion into a polynomial
change-of-variables API.  The generator criterion is the public bridge from
coefficient-ideal calculations to an arbitrary polynomial endomorphism.
-/

@[expose] public section

universe u v

namespace MvPolynomial.AlgHom

variable {R : Type u} [CommRing R]
variable {σ : Type v}

/-- Tag `07RD`: an `R`-algebra endomorphism of `MvPolynomial σ R` is congruent
to the identity modulo `I` when its error takes values in the extended
coefficient ideal `I.map MvPolynomial.C`. -/
@[stacks 07RD "polynomial endomorphism congruent to the identity"]
def IsCongruentToId
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (I : Ideal R) : Prop :=
  ∀ p, φ p - p ∈ Ideal.map MvPolynomial.C I

/-- Tag `07RD`: congruence to the identity modulo a coefficient ideal is
detected on the polynomial variables. -/
@[stacks 07RD "generator criterion for polynomial congruence to identity"]
theorem isCongruentToId_iff_sub_X_mem_map_C
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (I : Ideal R) :
    IsCongruentToId φ I ↔
      ∀ i, φ (MvPolynomial.X i) - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C I := sorry

/-- Tag `07RD`: an endomorphism congruent to the identity modulo a nilpotent
coefficient ideal acts invertibly on the underlying `R`-module. -/
@[stacks 07RD "unit polynomial endomorphism modulo a nilpotent ideal"]
theorem IsCongruentToId.isUnit
    {φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R} {I : Ideal R}
    (hI : IsNilpotent I) (hφ : IsCongruentToId φ I) :
    IsUnit φ.toLinearMap := sorry

/-- Tag `07RD`: an endomorphism congruent to the identity modulo a nilpotent
coefficient ideal is bijective. -/
@[stacks 07RD "bijective polynomial endomorphism modulo a nilpotent ideal"]
theorem IsCongruentToId.bijective
    {φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R} {I : Ideal R}
    (hI : IsNilpotent I) (hφ : IsCongruentToId φ I) :
    Function.Bijective φ := sorry

/-- Tag `07RD`: an endomorphism congruent to the identity modulo a nilpotent
coefficient ideal is surjective. -/
@[stacks 07RD "surjective polynomial endomorphism modulo a nilpotent ideal"]
theorem IsCongruentToId.surjective
    {φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R} {I : Ideal R}
    (hI : IsNilpotent I) (hφ : IsCongruentToId φ I) :
    Function.Surjective φ := sorry

end MvPolynomial.AlgHom

namespace MvPolynomial

variable {R : Type u} [CommRing R]
variable {σ : Type v}

/-- Tag `07RD`: substitution by variables differing from `X` by elements of a
nilpotent coefficient ideal is bijective. -/
@[stacks 07RD "bijective nilpotent polynomial variable perturbation"]
theorem aeval_bijective_of_nilpotent_perturbation
    (g : σ → MvPolynomial σ R) {I : Ideal R} (hI : IsNilpotent I)
    (hg : ∀ i, g i - X i ∈ Ideal.map C I) :
    Function.Bijective (aeval (R := R) g) := sorry

/-- Tag `07RD`: substitution by variables differing from `X` by elements of a
nilpotent coefficient ideal is surjective. -/
@[stacks 07RD "surjective nilpotent polynomial variable perturbation"]
theorem aeval_surjective_of_nilpotent_perturbation
    (g : σ → MvPolynomial σ R) {I : Ideal R} (hI : IsNilpotent I)
    (hg : ∀ i, g i - X i ∈ Ideal.map C I) :
    Function.Surjective (aeval (R := R) g) := sorry

end MvPolynomial
