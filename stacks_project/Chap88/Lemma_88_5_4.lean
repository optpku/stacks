/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Ring

/-!
# Lifting maps along a principal adic filtration

If `I = (a)` is principal, `B` is topologically of finite type, `a^c` annihilates
`Ext¹` of `NL_{B/A}^∧`, and `a` is a nonzerodivisor on an `I`-adically complete
algebra `C`, then any map `B →ₐ[A] C ⧸ a^n C` with `n > 2c` lifts to `C` up to
congruence modulo `a^{n-c} C`.
-/

@[expose] public section

universe u

namespace Algebra.NaiveCotangent.Adic

/-- Lemma 88.5.4: Let `I = (a)` be a principal ideal of a Noetherian ring `A`.
Let `B` be an object of (88.2.0.2). Assume given an integer `c ≥ 0` such that
`Ext¹_B(NL_{B/A}^∧, N)` is annihilated by `a^c` for all `B`-modules `N`. Let
`C` be an `I`-adically complete `A`-algebra such that `a` is a nonzerodivisor
on `C`. Let `n > 2c`. For any `A`-algebra map `ψn : B →ₐ[A] C ⧸ a^n C` there
exists an `A`-algebra map `φ : B →ₐ[A] C` such that `ψn` and `φ` agree as maps
into `C ⧸ a^{n-c} C`. -/
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
