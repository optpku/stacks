/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import stacks_project.Chap88.Definition_88_8_1_Derived
public import stacks_project.Chap88.Lemma_88_4_2_Jacobian

/-!
# Characterization of rig-smooth algebras

Lemma 88.4.2 equates rig-smoothness of an object of `C'` with Ext-annihilation
of the completed naive cotangent complex, factorization through the Jacobian,
and existence of a finite Jacobian cover.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.NaiveCotangent.Adic
open scoped PrimeSpectrum

/-- Lemma 88.4.2: for a Noetherian ring `A`, an ideal `I`, and an algebra `B`
topologically of finite type over `(A, I)`, equipped with a finite completed
presentation `P` and completed naive cotangent object `naiveCotangentObject I P`,
the following are equivalent: `B` is `RigSmooth` over `(A, I)`;
`naiveCotangentObject I P` in `D(B)` satisfies Lemma 15.85.10 (1), equivalently
(1)–(6) in this Noetherian finite-cohomology setting, with respect to the ideal
`I.map (algebraMap A B)`; some `I ^ c` has the property that every `a ∈ I ^ c`
factors on `J / J²` through the Jacobian; and `P` admits a finite Jacobian cover
`V({b_l}) ⊆ V(I B)` by elements elementary for square Jacobian minors. -/
@[stacks 0GAJ]
theorem Algebra.RigSmooth.tfae {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : NaiveCotangent.Adic.Presentation A B I ι) :
    List.TFAE
      ([RigSmooth I B,
        ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject I P)
          (I.map (algebraMap A B) ^ c),
        ∃ c : ℕ, ∀ a ∈ I ^ c, P.smulFactorsThroughJacobian a,
        P.HasJacobianCover]) :=
  sorry
