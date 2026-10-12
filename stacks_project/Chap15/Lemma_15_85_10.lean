/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.IdealPowerProjectivity
import StacksCheckRecall

/-!
# Lemma 15.85.10

The source TFAE is owned by the canonical two-term ideal-power projectivity API.  The chapter
entry retains the exact source tag and direct checks for both the general and Noetherian finite
forms.

@stack 0G9K
-/

@[expose] public section

open CategoryTheory
open PrimeSpectrum
open scoped PrimeSpectrum

universe u

@[stacks 0G9K "Lemma 15.85.10 (1)-(2)"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) =>
  (CategoryTheory.two_term_ideal_power_projectivity_tfae K I hKGE hKLE :
    List.TFAE [
      ∃ c : ℕ, CategoryTheory.twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R
          ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        Module.IsIdealProjective (I ^ c)
          ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)])

@[stacks 0G9K "Lemma 15.85.10 (1)-(6)"]
#check fun {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) =>
  (CategoryTheory.two_term_ideal_power_projectivity_tfae_of_isNoetherianRing
      K I hKGE hKLE hHneg1 hH0 :
    List.TFAE [
      ∃ c : ℕ, CategoryTheory.twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R
          ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        Module.IsIdealProjective (I ^ c)
          ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K),
      ∃ c : ℕ, CategoryTheory.twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c),
      Module.IsIdealPowerTorsion I
          ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s, Module.Projective (Localization.Away f)
              (LocalizedModule.Away f
                ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)),
      Module.IsIdealPowerTorsion I
          ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        ∃ s : Finset R,
          (↑s : Set R) ⊆ I ∧ V((↑s : Set R)) = V((I : Set R)) ∧
            ∀ f ∈ s, Module.Projective (Localization.Away f)
              (LocalizedModule.Away f
                ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)),
      Module.IsIdealPowerTorsion I
          ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        ∀ s : Finset R, (↑s : Set R) ⊆ I → V((↑s : Set R)) = V((I : Set R)) →
          ∀ f ∈ s, Module.Projective (Localization.Away f)
            (LocalizedModule.Away f
              ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K))])
