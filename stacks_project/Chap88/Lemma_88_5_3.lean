module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.AssociatedGraded

/-!
# Lifting maps using associated-graded size bounds

If `B` is topologically of finite type, `I ^ c` annihilates `Ext¹` of
`NL_{B/A}^∧`, and `C` is a Noetherian `I`-adically complete `A`-algebra,
then any map `B →ₐ[A] C ⧸ I ^ n C` with `n` large enough relative to
`d(Gr_I(C))` and `q(Gr_I(C))` lifts to `C` up to congruence modulo
`I ^ (n - (d + 1) * c) C`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry.IsBlowup

namespace Algebra.NaiveCotangent.Adic

/-- Lemma 88.5.3: Assume given an integer `c ≥ 0`, an ideal `I` of a
Noetherian ring `A`, `B` in (88.2.0.2) for `(A, I)` such that `I ^ c`
annihilates `Ext¹_B(NL_{B/A}^∧, N)` for any `B`-module `N`, and a
Noetherian `I`-adically complete `A`-algebra `C`. Write `d = d(Gr_I(C))`
and `q0 = q(Gr_I(C))` for the associated-graded invariants of Local
Cohomology, Section 51.22. Let
`n ≥ max (q0 + (d + 1) * c) (2 * (d + 1) * c + 1)`, and let
`ψn : B →ₐ[A] C ⧸ I ^ n C` be an `A`-algebra homomorphism. Then there
exists a map `φ : B →ₐ[A] C` of `A`-algebras such that `ψn` and `φ`
agree as maps into `C ⧸ I ^ (n - (d + 1) * c) C`. -/
@[stacks 0GAQ]
theorem exists_hom {A B C : Type u}
    [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing C] [IsNoetherianRing C]
    [Algebra A B] [Algebra A C] {I : Ideal A}
    [Algebra.TopologicallyFiniteType I B] (c : ℕ)
    (hann : Algebra.annihilatesExt1NaiveCotangent I B c)
    [IsAdicComplete (I.map (algebraMap A C)) C] {n : ℕ}
    (hn : max
        (associatedGradedUniformityThreshold (I.map (algebraMap A C)) +
          (1 + associatedGradedFiberDimension (I.map (algebraMap A C))) * c)
        (2 * (1 + associatedGradedFiberDimension (I.map (algebraMap A C))) * c + 1) ≤ n)
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B →ₐ[A] C,
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right
          (Nat.sub_le n ((1 + associatedGradedFiberDimension (I.map (algebraMap A C))) * c)))).comp ψn =
        (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^
            (n - (1 + associatedGradedFiberDimension (I.map (algebraMap A C))) * c))).comp φ :=
  sorry

end Algebra.NaiveCotangent.Adic
