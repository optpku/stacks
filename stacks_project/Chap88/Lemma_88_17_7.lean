module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import stacks_project.Chap88.Lemma_88_3_5_ExactSequence
public import stacks_project.Chap88.Lemma_88_15_1_FlatAway

/-!
# Lemma 88.17.7

If `A → B → C` are adic, topologically finite-type arrows of `WAdm^Noeth`
and `B → C` is rig-smooth, then the kernel of the Jacobi–Zariski map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)` from Lemma 88.3.5 is
annihilated by an ideal of definition of `C`.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
  [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
variable (P : Presentation A B I ι)
variable (Q : Presentation B C (I.map (algebraMap A B)) κ)

/-- Lemma 88.17.7: if `A → B → C` are adic, topologically finite-type arrows of
`WAdm^Noeth` and `B → C` is rig-smooth, then the kernel of
`homologyOneTensor` (the Jacobi–Zariski map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)` of Lemma 88.3.5) is
annihilated by an ideal of definition of `C`. -/
@[stacks 0GH2]
theorem homologyOneTensor_ker_annihilatedByIdealOfDefinition
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)] :
    ∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
      ∀ a ∈ J, ∀ x, homologyOneTensor I P Q x = 0 → a • x = 0 := sorry

/-- The kernel of `homologyOneTensor` is annihilated by an ideal of definition of
`C` in the sense that some such ideal is contained in the annihilator of the
kernel. -/
theorem homologyOneTensor_ker_annihilatedByIdealOfDefinition_spec
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)] :
    ∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
      J ≤ Module.annihilator C (LinearMap.ker (homologyOneTensor I P Q).hom) :=
  sorry

/-- Pointwise annihilation of `ker homologyOneTensor` by an ideal of definition
is equivalent to containment in the annihilator of that kernel. -/
theorem homologyOneTensor_ker_annihilatedByIdealOfDefinition_iff
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)] :
    (∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
        ∀ a ∈ J, ∀ x, homologyOneTensor I P Q x = 0 → a • x = 0) ↔
      ∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
        J ≤ Module.annihilator C (LinearMap.ker (homologyOneTensor I P Q).hom) :=
  sorry

/-- After localizing at a prime of `C` containing no ideal of definition, the
Jacobi–Zariski map `homologyOneTensor` is injective. -/
theorem homologyOneTensor_injective_at_prime_containsNoIdealOfDefinition
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)]
    (q : Ideal C) [q.IsPrime] (hq : q.ContainsNoIdealOfDefinition) :
    Function.Injective
      (LocalizedModule.map q.primeCompl (homologyOneTensor I P Q).hom) :=
  sorry

end Algebra.NaiveCotangent.Adic
