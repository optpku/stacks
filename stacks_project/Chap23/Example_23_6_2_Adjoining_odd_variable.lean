module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.DividedPowers
import StacksCheckRecall

@[expose] public section

/-!
# Adjoining an odd variable

The reusable algebra, parity reindexing, canonical divided powers, base inclusion, and mapping
property are owned by `NonnegGradedAlgebra.Adjoin.Odd`.  The coefficient recursion is exposed by
`Adjoin.Odd.IsCanonical`, while `Adjoin.Odd.dpAlgebra` is the bundled object used downstream.  This
source facade records the positive odd-degree specialization from Example 23.6.2.
-/

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]

section Source

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)
  (gammaA : NonnegGradedAlgebra.DividedPowers A)

/- Example 23.6.2 (Adjoining odd variable) (1): adjoining a variable in positive odd degree to a
divided-power graded algebra produces the bundled divided-power algebra `A⟨T⟩`. -/
@[stacks 09PH "(1)"]
#check
  ((fun (hd : Odd d) ↦ Adjoin.Odd.dpAlgebra A d gammaA hd) :
    ∀ hd : Odd d, DividedPowerGradedAlgebra.{u, v} R)

/- Example 23.6.2 (Adjoining odd variable) (2): the canonical structure satisfies
`gamma 0 (x + yT) = 1` and
`gamma (n + 1) (x + yT) = gammaA (n + 1) x + gammaA n x * yT` in coefficient coordinates. -/
@[stacks 09PH "(2)"]
#check
  ((fun (hd : Odd d) ↦
      ⟨(Adjoin.Odd.dividedPowers_isCanonical A d gammaA hd).zero,
        (Adjoin.Odd.dividedPowers_isCanonical A d gammaA hd).succ⟩) :
    ∀ hd : Odd d,
      (∀ z : Adjoin.Odd.PositiveCoeffs A,
        Adjoin.Odd.gammaCoords A d hd (Adjoin.Odd.dividedPowers A d gammaA hd) 0 z =
          Adjoin.Odd.ofEven A A.oneEven) ∧
        (∀ (n : ℕ) (x : A.evenPositivePart) (y : A.oddPart),
          Adjoin.Odd.gammaCoords A d hd (Adjoin.Odd.dividedPowers A d gammaA hd)
              (n + 1) (x, y) =
            (gammaA (n + 1) x, A.evenMulOdd (gammaA n x) y)))

/- Example 23.6.2 (Adjoining odd variable) (3): the base inclusion is a morphism of
divided-power graded algebras. -/
@[stacks 09PH "(3)"]
#check
  ((fun (hd : Odd d) ↦ Adjoin.Odd.inclusionDP A d gammaA hd) :
    ∀ hd : Odd d,
      NonnegGradedAlgebra.DividedPowers.Hom gammaA
        (Adjoin.Odd.dividedPowers A d gammaA hd))

/- Example 23.6.2 (Adjoining odd variable) (4): the explicit coefficient recursion and base
restriction uniquely determine the divided-power structure on the bundled extension. -/
@[stacks 09PH "(4)"]
#check
  ((fun (hd : Odd d) ↦ Adjoin.Odd.existsUnique_dividedPowers A d gammaA hd) :
    ∀ hd : Odd d,
      ∃! delta : NonnegGradedAlgebra.DividedPowers (Adjoin.Odd.algebra A d hd),
        Adjoin.Odd.IsCanonical A d gammaA hd delta)

end Source

#check @Adjoin.ShiftSum
#check @Adjoin.Odd.Piece
#check @Adjoin.Odd.algebra
#check @Adjoin.Odd.inclusion
#check @Adjoin.Odd.generator
#check @Adjoin.Odd.generator_sq
#check @Adjoin.Odd.lift
#check @Adjoin.Odd.lift_comp
#check @Adjoin.Odd.Coeffs
#check @Adjoin.Odd.PositiveCoeffs
#check @Adjoin.Odd.ofEven
#check @Adjoin.Odd.ofPositive
#check @Adjoin.Odd.gamma
#check @Adjoin.Odd.gamma_zero
#check @Adjoin.Odd.gamma_succ
#check @Adjoin.Odd.gamma_ofPositive
#check @Adjoin.Odd.IsGamma
#check @Adjoin.Odd.isGamma_iff
#check @Adjoin.Odd.existsUnique_gamma
#check @Adjoin.Odd.evenReindex
#check @Adjoin.Odd.positiveReindex
#check @Adjoin.Odd.dividedPowers
#check @Adjoin.Odd.dividedPowers_isCanonical
#check @Adjoin.Odd.IsCanonical.eq_dividedPowers
#check @Adjoin.Odd.existsUnique_dividedPowers
#check @Adjoin.Odd.dpAlgebra
#check @Adjoin.Odd.inclusionDP
#check @Adjoin.Odd.liftDP
#check @Adjoin.Odd.inclusionDP_comp_liftDP
#check @Adjoin.Odd.liftDP_generator
#check @Adjoin.Odd.liftDP_unique

end NonnegGradedAlgebra
