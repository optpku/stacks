/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.BaseChange.Bijective
public import ReasLib.RingTheory.AdicCompletion.Congruence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completion of ideal-power torsion modules

Finite generation identifies every ideal-power quotient of a ring with the
corresponding quotient of its adic completion.  The general base-change owner
then makes the canonical tensor unit bijective on ideal-power torsion modules.

@stack 0BNK
-/

@[expose] public section

open scoped TensorProduct

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Lemma 15.89.9 (0BNK), completion quotient form: if `I` is finitely
generated, then the canonical map from `R ⧸ I ^ n` to the corresponding
quotient of the `I`-adic completion is bijective. -/
@[stacks 0BNK "adic completion quotient map"]
theorem adicCompletion_quotientMap_bijective
    (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((I ^ n).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) := sorry
-- Proof strategy: use finite generation to identify the `I ^ n` quotient of the completion
-- with `R ⧸ I ^ n`, then compare the canonical quotient map with that equivalence.

/-- Lemma 15.89.9 (0BNK), completion specialization: the canonical map
`M ⟶ AdicCompletion I R ⊗[R] M` is bijective for every `I`-power torsion
module `M` when `I` is finitely generated. -/
@[stacks 0BNK "adic completion tensor base change"]
theorem tensorAdicCompletion_bijective_of_isIdealPowerTorsion
    (hI : I.FG) (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := sorry
-- Proof strategy: apply the generic ideal-power base-change theorem, discharging each
-- positive quotient hypothesis with `adicCompletion_quotientMap_bijective`.

end
