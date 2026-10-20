/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.AssociatedGraded
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting maps into Noetherian complete algebras

Annihilation of the completed naive cotangent Ext¹ gives lifts of residue
algebra maps up to a precision controlled by associated-graded invariants.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry.IsBlowup

namespace Algebra.NaiveCotangent.Adic

/-- Let `I` be an ideal of a Noetherian ring `A`, and let `B` be a
topologically finite type `A`-algebra for `I` such that `I ^ c` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. For a Noetherian
`I`-adically complete `A`-algebra `C`, write `d` and `q0` for its
associated-graded fibre dimension and uniformity threshold. If
`n ≥ max (q0 + (d + 1) * c) (2 * (d + 1) * c + 1)`, every residue map
`B →ₐ[A] C ⧸ I ^ n C` agrees modulo `I ^ (n - (d + 1) * c) C` with
an `A`-algebra map `B →ₐ[A] C`. -/
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
