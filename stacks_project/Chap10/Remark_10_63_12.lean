module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Domain
public import ReasLib.RingTheory.MvPolynomial.SquareZero
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.63.12

The counterexample is the countable specialization of the reusable square-zero
polynomial quotient.  The source entry checks the canonical owner directly;
it does not retain chapter-specific aliases or theorem wrappers.
@stack 05BX
-/

universe u

open MvPolynomial IsLocalRing

section

variable (k : Type u) [Field k]

@[stacks 05BX "countable square-zero polynomial quotient"]
#check (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))

@[stacks 05BX "square-zero augmentation"]
#check (MvPolynomial.SquareZero.augmentation (σ := ℕ) (k := k))

@[stacks 05BX "square-zero augmentation surjectivity"]
#check (MvPolynomial.SquareZero.augmentation_surjective (σ := ℕ) (k := k) :
  Function.Surjective (MvPolynomial.SquareZero.augmentation (σ := ℕ) (k := k)))

@[stacks 05BX "square-zero unit criterion"]
#check (MvPolynomial.SquareZero.isUnit_iff_augmentation_ne_zero (σ := ℕ) (k := k) :
  ∀ x : MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k),
    IsUnit x ↔ MvPolynomial.SquareZero.augmentation (σ := ℕ) (k := k) x ≠ 0)

@[stacks 05BX "square-zero local ring"]
#check (inferInstance :
  IsLocalRing (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)))

@[stacks 05BX "square-zero residue field"]
#check (MvPolynomial.SquareZero.residueFieldEquiv (σ := ℕ) (k := k))

@[stacks 05BX "base-field exact associated primes"]
#check (associatedPrimesOfModule.eq_singleton_bot
    (R := k) (M := MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) :
  associatedPrimesOfModule k
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) = {⊥})

@[stacks 05BX "base-field radical associated primes"]
#check (associatedPrimes.eq_singleton_bot
    (R := k) (M := MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) :
  associatedPrimes k
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) = {⊥})

@[stacks 05BX "self associated primes are empty"]
#check (MvPolynomial.SquareZero.associatedPrimesOfModule_self_eq_empty
    (σ := ℕ) (k := k) :
  associatedPrimesOfModule
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) = ∅)

@[stacks 05BX "associated-prime contraction failure"]
#check (MvPolynomial.SquareZero.comap_not_superset (σ := ℕ) (k := k) :
  ¬ associatedPrimesOfModule k
        (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) ⊆
      Ideal.comap
          (algebraMap k (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))) ''
        associatedPrimesOfModule
          (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))
          (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)))

end
