/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.ResidueField
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.7.2: If `E` is an injective hull of the residue field of the local ring
`R`, then an `IsLocalRing.maximalIdeal R`-power torsion module whose submodule killed by
the maximal ideal has dimension `n` embeds in `Fin n → E`. -/
@[stacks 08Z3] #check (Module.exists_injective_to_pi_of_isIdealPowerTorsion :
    (R : Type u) → (E : Type v) → (M : Type w) → [CommRing R] → [IsLocalRing R] →
      [AddCommGroup E] → [Module R E] → [Module.Injective R E] →
      [AddCommGroup M] → [Module R M] →
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) → ι.IsInjectiveHull →
      (Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) M) →
      (n : ℕ) →
      Nonempty ((IsLocalRing.maximalIdeal R).powerAnnihilatedSubmodule M 1 ≃ₗ[R]
        (Fin n → IsLocalRing.ResidueField R)) →
      ∃ f : M →ₗ[R] (Fin n → E), Function.Injective f)
