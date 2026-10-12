/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Basic
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Lemma 87.8.3

Pre-admissibility descends along a continuous taut homomorphism of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsPreadmissibleRing

/-- Lemma 87.8.3: In the situation above, if `B` is pre-admissible, then `A` is
pre-admissible. The situation is a continuous taut homomorphism `φ : A →+* B` of
linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every
open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXN]
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsPreadmissibleRing A :=
  sorry

/-- If `J` is an ideal of definition of `B` and `I` is an open ideal of `A` with
`Ideal.map φ I ≤ J`, then `I` is an ideal of definition of `A`. -/
theorem isIdealOfDefinition_of {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) {I : Ideal A}
    (hI : IsOpen (I : Set A)) (hmap : Ideal.map φ I ≤ J) :
    TopologicalRing.Ideal.IsIdealOfDefinition I :=
  sorry

end TopologicalRing.IsPreadmissibleRing
