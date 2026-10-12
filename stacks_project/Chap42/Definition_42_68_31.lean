/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 42.68.31: the tame symbol of a one-dimensional Noetherian local domain is the
bimultiplicative extension of the scalar-quotient determinant to its fraction-field units. -/
@[stacks 02Q1] #check
  (TameSymbol.value :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K],
      ringKrullDim A = 1 →
        Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
