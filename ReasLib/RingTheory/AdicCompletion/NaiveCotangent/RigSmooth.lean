/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.JacobiZariski
public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.Topology.Adic.Prime
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Rig-smoothness and completed cotangent homology

For adic, topologically finite-type towers of Noetherian adic rings with
rig-smooth second arrow, an ideal of definition annihilates the kernel of
the Jacobi–Zariski map on degree-one completed naive cotangent homology.
-/

@[expose] public section

universe u

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

/-- For an adic, topologically finite-type tower of Noetherian adic rings with
rig-smooth second arrow, an ideal of definition of the final ring annihilates
the kernel of the Jacobi–Zariski map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)`. -/
@[stacks 0GH2]
theorem homologyOneTensor_ker_annihilatedByIdealOfDefinition
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)] :
    ∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
      ∀ a ∈ J, ∀ x, homologyOneTensor I P Q x = 0 → a • x = 0 := sorry

/-- For an adic, topologically finite-type tower of Noetherian adic rings with
rig-smooth second arrow, the Jacobi–Zariski map on degree-one completed naive
cotangent homology is injective after localization at a prime of the final
ring containing no ideal of definition. -/
theorem homologyOneTensor_injective_at_prime_containsNoIdealOfDefinition
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hAB : (algebraMap A B).IsAdicHom)
    [RingHom.RigSmooth (algebraMap B C)]
    (q : Ideal C) [q.IsPrime] (hq : q.ContainsNoIdealOfDefinition) :
    Function.Injective
      (LocalizedModule.map q.primeCompl (homologyOneTensor I P Q).hom) :=
  sorry

end Algebra.NaiveCotangent.Adic
