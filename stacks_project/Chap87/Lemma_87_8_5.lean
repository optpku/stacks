/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Lemma 87.8.5

Adic rings with a finitely generated ideal of definition descend along a
continuous taut homomorphism of linearly topologized rings with faithfully
flat open quotients, when the source is complete.
-/

@[expose] public section

universe u v

open RingHom

namespace TopologicalRing.IsAdicRing

/-- Lemma 87.8.5 (1): In the situation above, if `B` is adic and has a finitely
generated ideal of definition and `A` is complete, then `A` is adic. The
situation is a continuous taut homomorphism `φ : A →+* B` of linearly
topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every open
ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. Completeness of `A` means
separatedness together with completeness of the additive uniformity. -/
@[stacks 0GXQ]
theorem of_faithfullyFlatOpenQuotients {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    (hBfg : ∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) :
    IsAdicRing A :=
  sorry

/-- Lemma 87.8.5 (2): In the situation above, if `B` is adic and has a finitely
generated ideal of definition and `A` is complete, then `A` has a finitely
generated ideal of definition. -/
@[stacks 0GXQ]
theorem exists_fg_isIdealOfDefinition {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    (hBfg : ∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) :
    ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I :=
  sorry

end TopologicalRing.IsAdicRing
