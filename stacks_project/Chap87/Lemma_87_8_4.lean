/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Lemma 87.8.4

Weakly pre-adic rings descend along a continuous taut homomorphism of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsWeaklyPreadicRing

/-- Lemma 87.8.4: In the situation above, if `B` is weakly pre-adic, then `A` is
weakly pre-adic. The situation is a continuous taut homomorphism `φ : A →+* B` of
linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every
open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXP]
theorem of_faithfullyFlatOpenQuotients {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsWeaklyPreadicRing A :=
  sorry

/-- If `I` is an ideal of definition of `A`, then `(I ^ n).closure` is open for
every `n ≥ 1`. -/
theorem isOpen_closure_pow {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyPreadicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    {I : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) {n : ℕ}
    (hn : 1 ≤ n) : IsOpen ((I ^ n).closure : Set A) :=
  sorry

end TopologicalRing.IsWeaklyPreadicRing
