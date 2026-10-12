/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_4_12_Completed
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_15_8_RigFlat

/-!
# Adic and Noetherian instances for completed tensors

The completed tensor of adic Noetherian algebras remains adic Noetherian, so
the canonical right inclusion may carry `RingHom.RigFlat`.
-/

@[expose] public section

universe u

namespace Algebra.TensorProduct.Completed

/-- The completed tensor product of adic Noetherian algebras, formed over a
rig-flat left structure map and an adic right structure map, remains adic. -/
instance instIsAdicRing {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing B] [IsNoetherianRing C]
    [RingHom.RigFlat (algebraMap A B)]
    [hC : Fact ((algebraMap A C).IsAdicHom)] :
    TopologicalRing.IsAdicRing (Completed A B C) :=
  sorry

/-- The completed tensor product of adic Noetherian algebras remains Noetherian
when the left structure map is rig-flat. -/
instance instIsNoetherianRing {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [RingHom.RigFlat (algebraMap A B)]
    [hC : Fact ((algebraMap A C).IsAdicHom)] :
    IsNoetherianRing (Completed A B C) :=
  sorry

end Algebra.TensorProduct.Completed
