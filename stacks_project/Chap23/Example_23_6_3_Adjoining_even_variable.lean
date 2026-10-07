module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.DividedPowers
import StacksCheckRecall

@[expose] public section

/-!
# Adjoining an even variable

The reusable algebra, divided-monomial convolution, parity reindexing, canonical divided powers,
base inclusion, and mapping property are owned by `NonnegGradedAlgebra.Adjoin.Even`.  Its universal
property records all divided monomials, not merely the first generator.  Explicit coefficient
formulas are exposed through `Adjoin.Even.IsCanonical`, while `Adjoin.Even.dpAlgebra` is the bundled
object used downstream.
-/

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]

section Source

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)
  (gammaA : NonnegGradedAlgebra.DividedPowers A)

/- Example 23.6.3 (Adjoining even variable) (1): adjoining a variable in positive even degree to a
divided-power graded algebra produces the bundled divided-power algebra `A⟨T⟩`. -/
@[stacks 09PI "(1)"]
#check
  ((fun (hpos : 0 < d) (hd : Even d) ↦ Adjoin.Even.dpAlgebra A d gammaA hd hpos) :
    ∀ (_ : 0 < d) (_ : Even d), DividedPowerGradedAlgebra.{u, v} R)

/- Example 23.6.3 (Adjoining even variable) (2): divided monomials multiply with the canonical
coefficient `Nat.choose (i + j) i`. -/
@[stacks 09PI "(2)"]
#check
  ((fun (_ : 0 < d) (_ : Even d) ↦ Adjoin.Even.monomial_mul A) :
    ∀ (_ : 0 < d) (_ : Even d) (i j : ℕ) (x y : A.evenPart),
      Adjoin.Even.mul A (Adjoin.Even.monomial A i x) (Adjoin.Even.monomial A j y) =
        Adjoin.Even.monomial A (i + j)
          (Nat.choose (i + j) i • A.evenMul x y))

/- Example 23.6.3 (Adjoining even variable) (3): the divided power of a positive-tail coefficient
family is the sum over finitely supported exponent distributions of total weight `n`. -/
@[stacks 09PI "(3)"]
#check
  ((fun (_ : 0 < d) (_ : Even d) ↦ Adjoin.Even.tailGamma_apply A) :
    ∀ (_ : 0 < d) (_ : Even d) (n : ℕ) (x : ℕ+ →₀ A.evenPart),
      Adjoin.Even.tailGamma A n x =
        (Finset.finsuppAntidiag x.support n).sum fun e ↦ Adjoin.Even.distributionTerm A x e)

/- Example 23.6.3 (Adjoining even variable) (4): in canonical coefficient coordinates the full
divided-power operation is the antidiagonal convolution of `gammaA` with the positive-tail
formula. -/
@[stacks 09PI "(4)"]
#check
  ((fun (hpos : 0 < d) (hd : Even d) ↦
      (Adjoin.Even.dividedPowers_isCanonical A d gammaA hd hpos).coefficients) :
    ∀ (hpos : 0 < d) (hd : Even d) (n : ℕ) (z : Adjoin.Even.PositiveCoeffs A),
      Adjoin.Even.gammaCoords A d hd (Adjoin.Even.dividedPowers A d gammaA hd hpos) n z =
        (Finset.antidiagonal n).sum fun ab ↦
          Adjoin.Even.mul A
            (Adjoin.Even.monomial A 0 (gammaA ab.1 z.constant))
            (Adjoin.Even.tailGamma A ab.2 z.tail))

/- Example 23.6.3 (Adjoining even variable) (5): the base inclusion is a morphism of
divided-power graded algebras. -/
@[stacks 09PI "(5)"]
#check
  ((fun (hpos : 0 < d) (hd : Even d) ↦ Adjoin.Even.inclusionDP A d gammaA hd hpos) :
    ∀ (hpos : 0 < d) (hd : Even d),
      NonnegGradedAlgebra.DividedPowers.Hom gammaA
        (Adjoin.Even.dividedPowers A d gammaA hd hpos))

/- Example 23.6.3 (Adjoining even variable) (6): the canonical divided powers send `T^(i)` to
`T^(n*i)` in coefficient coordinates. -/
@[stacks 09PI "(6)"]
#check
  ((fun (hpos : 0 < d) (hd : Even d) ↦
      (Adjoin.Even.dividedPowers_isCanonical A d gammaA hd hpos).tPower) :
    ∀ (hpos : 0 < d) (hd : Even d) (n : ℕ) (i : ℕ+),
      Adjoin.Even.gammaCoords A d hd (Adjoin.Even.dividedPowers A d gammaA hd hpos)
          n (Adjoin.Even.tPower A i) =
        Adjoin.Even.monomial A (n * (i : ℕ)) A.oneEven)

/- Example 23.6.3 (Adjoining even variable) (7): the explicit formulas and base restriction
determine a unique divided-power structure on the bundled extension. -/
@[stacks 09PI "(7)"]
#check
  ((fun (hpos : 0 < d) (hd : Even d) ↦
      Adjoin.Even.existsUnique_dividedPowers A d gammaA hd hpos) :
    ∀ (hpos : 0 < d) (hd : Even d),
      ∃! delta : NonnegGradedAlgebra.DividedPowers (Adjoin.Even.algebra A d hd),
        Adjoin.Even.IsCanonical A d gammaA hd delta)

end Source

#check @Adjoin.ShiftSum
#check @Adjoin.Even.Piece
#check @Adjoin.Even.algebra
#check @Adjoin.Even.inclusion
#check @Adjoin.Even.generator
#check @Adjoin.Even.dividedMonomial
#check @Adjoin.Even.DividedMonomials
#check @Adjoin.Even.lift
#check @Adjoin.Even.lift_comp
#check @Adjoin.Even.Coeffs
#check @Adjoin.Even.PositiveCoeffs
#check @Adjoin.Even.PositiveCoeffs.constant
#check @Adjoin.Even.PositiveCoeffs.tail
#check @Adjoin.Even.monomial
#check @Adjoin.Even.one
#check @Adjoin.Even.ofPositive
#check @Adjoin.Even.tPower
#check @Adjoin.Even.PositiveCoeffs.toCoeffs
#check @Adjoin.Even.PositiveCoeffs.toCoeffs_add
#check @Adjoin.Even.PositiveCoeffs.toCoeffs_smul
#check @Adjoin.Even.mul
#check @Adjoin.Even.monomial_mul
#check @Adjoin.Even.distributionTerm
#check @Adjoin.Even.tailGamma
#check @Adjoin.Even.gamma
#check @Adjoin.Even.gamma_ofPositive
#check @Adjoin.Even.gamma_tPower
#check @Adjoin.Even.IsGamma
#check @Adjoin.Even.existsUnique_gamma
#check @Adjoin.Even.evenReindex
#check @Adjoin.Even.positiveReindex
#check @Adjoin.Even.dividedPowers
#check @Adjoin.Even.dividedPowers_isCanonical
#check @Adjoin.Even.IsCanonical.eq_dividedPowers
#check @Adjoin.Even.existsUnique_dividedPowers
#check @Adjoin.Even.dpAlgebra
#check @Adjoin.Even.inclusionDP
#check @Adjoin.Even.liftDP
#check @Adjoin.Even.inclusionDP_comp_liftDP
#check @Adjoin.Even.liftDP_generator
#check @Adjoin.Even.liftDP_unique

end NonnegGradedAlgebra
