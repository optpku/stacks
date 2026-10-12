/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.Algebra.Module.IdealProjective.Ext
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power projectivity for two-term derived modules

This file owns the source-facing equivalences between Ext-annihilation, cohomological
annihilation/projectivity, and finite basic-open localization criteria.

@stack 0G9K
-/

@[expose] public section

open CategoryTheory
open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/-- Lemma 15.85.10: for a two-term derived module, a power of `I` satisfying the basic
Ext-annihilation conditions is equivalent to a power annihilating `H⁻¹` and making `H⁰`
`I`-projective. -/
@[stacks 0G9K "Lemma 15.85.10 (1)-(2)"]
theorem two_term_ideal_power_projectivity_tfae
    (K : DMod) (I : Ideal R) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K)
    ] := sorry
/- Proof strategy: use the two-term truncation triangle to identify annihilation of
`Ext¹_R(K, -)` by `I^c` with annihilation of `H⁻¹(K)` plus the Ext-one criterion for
`I^c`-projectivity of `H⁰(K)`.  Apply the canonical `Module.IsIdealProjective` Ext criterion in
both directions and finish the two-condition TFAE. -/

/-- Lemma 15.85.10, Noetherian finite case: the preceding conditions are also equivalent to
finite-test Ext-annihilation and to the three finite basic-open projectivity criteria in the
source statement. -/
@[stacks 0G9K "Lemma 15.85.10 (1)-(6)"]
theorem two_term_ideal_power_projectivity_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K)) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K),
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s,
              Module.Projective (Localization.Away f)
                (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          (↑s : Set R) ⊆ I ∧
            V((↑s : Set R)) = V((I : Set R)) ∧
              ∀ f ∈ s,
                Module.Projective (Localization.Away f)
                  (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∀ s : Finset R,
          (↑s : Set R) ⊆ I →
            V((↑s : Set R)) = V((I : Set R)) →
              ∀ f ∈ s,
                Module.Projective (Localization.Away f)
                  (LocalizedModule.Away f ((H^0).obj K))
    ] := sorry
/- Proof strategy: combine `two_term_ideal_power_projectivity_tfae` with the Noetherian
finite-module form of two-term Ext annihilation.  Rewrite bounded ideal-power annihilation as
`Module.IsIdealPowerTorsion`, then apply the finite basic-open characterizations of
`Module.IsIdealProjective` and their finite-cover refinements to obtain conditions (4)-(6);
assemble the six implications with `List.tfae_finish`. -/

end

end CategoryTheory
