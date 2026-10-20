/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Lifting maps along a principal adic filtration

Uniform annihilation of the completed naive cotangent Ext group gives lifts
to a complete algebra on which the generator of the ideal is a nonzerodivisor.
-/

@[expose] public section

universe u

namespace Algebra.NaiveCotangent.Adic

/-- Let `I = (a)` be a principal ideal of a Noetherian ring `A`, and let `B` be
an `I`-adically complete `A`-algebra with finite-type special fiber. If `a^c`
annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`, then every
`A`-algebra map `B → C/a^n C` with `n > 2c` agrees modulo `a^{n-c} C` with an
`A`-algebra map `B → C`, provided `C` is `I`-adically complete and `a` is a
nonzerodivisor on `C`. -/
@[stacks 0AK6]
theorem exists_hom_of_nonzerodivisor {A B C : Type u}
    [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {I : Ideal A} {a : A} (hI : I = Ideal.span {a})
    [Algebra.TopologicallyFiniteType I B] (c : ℕ)
    (hann : Algebra.annihilatesExt1NaiveCotangent I B c)
    [IsAdicComplete (I.map (algebraMap A C)) C] (ha : IsSMulRegular C a)
    {n : ℕ} (hn : 2 * c < n)
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B →ₐ[A] C,
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.sub_le n c))).comp ψn =
        (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - c))).comp φ :=
  sorry

end Algebra.NaiveCotangent.Adic
