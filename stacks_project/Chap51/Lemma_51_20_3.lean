/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AdicUniformity
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 51.20.3: for every positive `n`, some later ideal-power quotient map
`A ⧸ I ^ m ⟶ A ⧸ I ^ n` induces zero on `Tor` in every degree strictly above
the local-cohomological dimension of `I`. This is condition (6) of Lemma 51.20.2,
and hence is equivalent to its lift and Ext conditions for these finite modules. -/
@[stacks 0EH1] #check (Ideal.LocalCohomology.exists_powerQuotientMap_torVanishesAbove_dimension :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n : ℕ) (_ : 1 ≤ n),
    ∃ (m : ℕ) (h : n < m),
      ∀ (N : ModuleCat.{u} A) (i : ℕ),
        Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing < (i : ℤ) →
          ((Tor (ModuleCat.{u} A) i).map
            (ModuleCat.ofHom (AdicCompletion.transitionMap I A h.le))).app N = 0)
