/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Definition_111_18_1
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.18.2: for Noetherian rings, Algebra Definition 10.105.1 catenarity
(`IsCatenaryRing`) agrees with Definition 111.18.1 height additivity of nested primes. -/
@[stacks 0CT5]
#check (isCatenaryRing_iff_height_additive :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A],
    IsCatenaryRing A ↔
      ∀ ⦃p₁ p₂ p₃ : PrimeSpectrum A⦄, p₁ ≤ p₂ → p₂ ≤ p₃ →
        (p₃.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height =
          (p₃.asIdeal.map (Ideal.Quotient.mk p₂.asIdeal)).height +
            (p₂.asIdeal.map (Ideal.Quotient.mk p₁.asIdeal)).height)
