/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalIso
import StacksCheckRecall

@[expose] public section

universe u v

namespace Algebra.IsLocalIso

/- Lemma 61.3.6: if `A → B` is a local isomorphism, then there exist `n ≥ 0`,
elements `g₁, …, gₙ` in `B` generating the unit ideal, and elements `f₁, …, fₙ`
in `A` such that `A_{f_i} ≅ B_{g_i}` as `A`-algebras. -/
@[stacks 096J] #check (Algebra.IsLocalIso.exists_finset_localization_away :
  ∀ {R : Type u} {S : Type v}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [IsLocalIso R S],
      ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, ∃ f : R, IsLocalization.Away f (Localization.Away g))

end Algebra.IsLocalIso
