/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power torsion detected by localization families

For a finite generating family of an ideal, vanishing of the first
power-torsion stage, vanishing of every positive stage, and injectivity of the
principal-open localization-family map are equivalent.

@stack 05EA
-/

@[expose] public section

universe u v w

namespace LocalizedModule.Away.Cech

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} [Finite ι]

/-- If a finite family spans `I` and its localization-family map is injective,
then every positive `I`-power torsion stage vanishes. -/
@[stacks 05EA "positive ideal-power torsion detected by localization"]
theorem powerTorsion_eq_bot_of_familyMap_injective
    (I : Ideal R) (f : ι → R) (hI : Ideal.span (Set.range f) = I)
    (hf : Function.Injective (familyMap M f)) (n : ℕ+) :
    I.powerTorsion M (n : ℕ) = ⊥ := sorry
-- Proof strategy: use the Cech kernel criterion to turn `hf` into vanishing of the torsion
-- submodule for the generating set, then compare `I ^ n` with products of those generators.

/-- Lemma 15.89.3 (05EA): for a finite generating family `f` of `I`,
vanishing of `M[I]`, vanishing of every positive `I`-power torsion stage, and
injectivity of the map to the family of away localizations are equivalent. -/
@[stacks 05EA "ideal-power torsion and away localizations"]
theorem powerTorsion_eq_bot_tfae
    (I : Ideal R) (f : ι → R) (hI : Ideal.span (Set.range f) = I) :
    List.TFAE [
      I.powerTorsion M 1 = ⊥,
      ∀ n : ℕ+, I.powerTorsion M (n : ℕ) = ⊥,
      Function.Injective (familyMap M f)
    ] := sorry
-- Proof strategy: prove `(1) → (3)` with the finite-family Cech kernel criterion,
-- `(3) → (2)` by `powerTorsion_eq_bot_of_familyMap_injective`, and specialize `(2)` at `1`.

end LocalizedModule.Away.Cech
