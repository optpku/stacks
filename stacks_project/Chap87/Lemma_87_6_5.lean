/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic

/-!
# Lemma 87.6.5

A continuous taut homomorphism from a pre-adic ring with a finitely generated
ideal of definition into a complete linearly topologized ring is adic, and the
target is adic with a finitely generated ideal of definition.
-/

@[expose] public section

universe u v

open scoped Topology
open TopologicalRing

namespace RingHom.IsTaut

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [T2Space B] [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]

/-- Lemma 87.6.5 (1): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `B` is adic. -/
@[stacks 0APU]
theorem isAdicRing {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdicRing B :=
  sorry

/-- Lemma 87.6.5 (2): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `B` has a finitely generated
ideal of definition. -/
@[stacks 0APU]
theorem exists_fg_isIdealOfDefinition {φ : A →+* B} (hcont : Continuous φ)
    (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J :=
  sorry

/-- Lemma 87.6.5 (3): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `φ` is adic. -/
@[stacks 0APU]
theorem exists_isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
      IsAdic (Ideal.map φ I) :=
  sorry

/-- If `I` is a finitely generated ideal of definition of `A`, then the topology
on `B` is the `I`-adic topology. -/
theorem isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    {I : Ideal A} (hIfg : I.FG) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdic (Ideal.map φ I) :=
  sorry

end

/-- Once `B` is pre-adic, the homomorphism `φ` is adic in the sense of
`RingHom.IsAdicHom`. -/
theorem isAdicHom {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
    [CommRing B] [TopologicalSpace B] [IsPreadicRing B] [T2Space B]
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    φ.IsAdicHom :=
  sorry

end RingHom.IsTaut
