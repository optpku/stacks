module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Cofinal adic filtrations

A power containment between two ideals induces a comparison map between their
adic completions.  Mutual positive-power containments identify the two
completions and preserve adic completeness.

@stack 0319
-/

@[expose] public section

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]
variable (A B : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- A power containment of ideals induces the corresponding containment of
submodule filtrations. -/
theorem pow_smul_top_le_of_pow_le {k n : ℕ} (hAB : A ^ k ≤ B) :
    A ^ (k * n) • (⊤ : Submodule R M) ≤ B ^ n • (⊤ : Submodule R M) := sorry

/-- The quotient-level family underlying the comparison of the `A`-adic and
`B`-adic completions. -/
noncomputable def comparisonFamily (k : ℕ) (hAB : A ^ k ≤ B) (n : ℕ) :
    AdicCompletion A M →ₗ[R] M ⧸ (B ^ n • ⊤ : Submodule R M) :=
  (Submodule.factor (pow_smul_top_le_of_pow_le A B M hAB)).comp
    (AdicCompletion.eval A M (k * n))

/-- The quotient-level comparison family commutes with the inverse-system
transition maps. -/
theorem comparisonFamily_compatible (k : ℕ) (hAB : A ^ k ≤ B)
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap B M hmn ∘ₗ comparisonFamily A B M k hAB n =
      comparisonFamily A B M k hAB m := sorry

/-- The canonical comparison from the `A`-adic completion to the `B`-adic
completion induced by `A ^ k ≤ B`. -/
noncomputable def comparisonMapOfPowLe (k : ℕ) (hAB : A ^ k ≤ B) :
    AdicCompletion A M →ₗ[R] AdicCompletion B M :=
  AdicCompletion.lift B (comparisonFamily A B M k hAB)
    (comparisonFamily_compatible A B M k hAB)

/-- The comparison map preserves the canonical image of the original module. -/
@[simp]
theorem comparisonMapOfPowLe_of (k : ℕ) (hAB : A ^ k ≤ B) (x : M) :
    comparisonMapOfPowLe A B M k hAB (AdicCompletion.of A M x) =
      AdicCompletion.of B M x := sorry

/-- Under mutual positive-power containments, the two comparison maps compose
to the identity on the `B`-adic completion. -/
theorem comparisonMapOfPowLe_comp (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hAB : A ^ c ≤ B) (hBA : B ^ d ≤ A) :
    (comparisonMapOfPowLe A B M c hAB).comp
        (comparisonMapOfPowLe B A M d hBA) =
      LinearMap.id := sorry

/-- Mutual positive-power containments identify the corresponding adic
completions. -/
noncomputable def linearEquivOfPowLe
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hAB : A ^ c ≤ B) (hBA : B ^ d ≤ A) :
    AdicCompletion A M ≃ₗ[R] AdicCompletion B M :=
  LinearEquiv.ofLinear
    (comparisonMapOfPowLe A B M c hAB) (comparisonMapOfPowLe B A M d hBA)
    (comparisonMapOfPowLe_comp A B M c d hc hd hAB hBA) (comparisonMapOfPowLe_comp B A M d c hd hc hBA hAB)

/-- The equivalence of cofinal completions preserves the image of the original
module. -/
@[simp]
theorem linearEquivOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hAB : A ^ c ≤ B) (hBA : B ^ d ≤ A) (x : M) :
    linearEquivOfPowLe A B M c d hc hd hAB hBA (AdicCompletion.of A M x) =
      AdicCompletion.of B M x := sorry

/-- Adic completeness is invariant under replacing an ideal by a cofinal
ideal-power filtration. -/
theorem isAdicComplete_iff_of_pow_le
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hAB : A ^ c ≤ B) (hBA : B ^ d ≤ A) :
    IsAdicComplete A M ↔ IsAdicComplete B M := sorry

/-- The comparison of adic completions of a ring preserves the multiplicative identity. -/
theorem comparisonMapOfPowLe_one (k : ℕ) (hAB : A ^ k ≤ B) :
    comparisonMapOfPowLe A B R k hAB 1 = 1 := sorry

/-- The comparison of adic completions of a ring preserves multiplication. -/
theorem comparisonMapOfPowLe_mul (k : ℕ) (hAB : A ^ k ≤ B)
    (first second : AdicCompletion A R) :
    comparisonMapOfPowLe A B R k hAB (first * second) =
      comparisonMapOfPowLe A B R k hAB first * comparisonMapOfPowLe A B R k hAB second :=
  sorry

/-- A power containment induces a ring homomorphism between the corresponding adic
completions. -/
noncomputable def comparisonRingHomOfPowLe (k : ℕ) (hAB : A ^ k ≤ B) :
    AdicCompletion A R →+* AdicCompletion B R :=
  (AlgHom.ofLinearMap (comparisonMapOfPowLe A B R k hAB)
    (comparisonMapOfPowLe_one A B k hAB) (comparisonMapOfPowLe_mul A B k hAB)).toRingHom

/-- Mutual positive-power containments induce a ring equivalence between the corresponding
adic completions. -/
noncomputable def ringEquivOfPowLe
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hAB : A ^ c ≤ B) (hBA : B ^ d ≤ A) :
    AdicCompletion A R ≃+* AdicCompletion B R where
  toAddEquiv := (linearEquivOfPowLe A B R c d hc hd hAB hBA).toAddEquiv
  map_mul' := comparisonMapOfPowLe_mul A B c hAB

end AdicCompletion
