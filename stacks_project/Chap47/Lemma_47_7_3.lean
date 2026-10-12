/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.MaximalIdeal
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.7.3 (1): If `E` is an injective hull of the residue field of a
Noetherian local ring `R`, then the submodules of `E` annihilated by positive powers
of `IsLocalRing.maximalIdeal R` exhaust `E`. -/
@[stacks 08Z4] #check
  (LinearMap.IsInjectiveHull.maximalIdealPowerAnnihilatedStagesSup_eq_top :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (iota : IsLocalRing.ResidueField R →ₗ[R] E),
      iota.IsInjectiveHull →
        (IsLocalRing.maximalIdeal R).powerAnnihilatedStagesSup E = ⊤)

/- Lemma 47.7.3 (2): For every positive `n`, the submodule
`E[(IsLocalRing.maximalIdeal R) ^ n]`, equipped with its canonical
`R ⨸ (IsLocalRing.maximalIdeal R) ^ n`-module structure, is an injective hull of
the residue field over that quotient ring. -/
@[stacks 08Z4] #check
  (LinearMap.IsInjectiveHull.maximalIdealPowKernelAnnihilator :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (iota : IsLocalRing.ResidueField R →ₗ[R] E), iota.IsInjectiveHull →
        (n : ℕ+) →
          (iota.toKernelAnnihilator
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n : ℕ)))
            Ideal.Quotient.mk_surjective).IsInjectiveHull)
