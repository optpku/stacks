module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.RigSmooth
import StacksCheckRecall

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

/- Lemma 88.17.7: the kernel of the completed Jacobi–Zariski homology map
is annihilated by an ideal of definition when the second arrow is rig-smooth. -/
@[stacks 0GH2] #check
  (Algebra.NaiveCotangent.Adic.homologyOneTensor_ker_annihilatedByIdealOfDefinition :
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]
      [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
      (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
      [Algebra.TopologicallyFiniteType I C]
      {ι κ : Type u} [Fintype ι] [Fintype κ]
      (P : Presentation A B I ι)
      (Q : Presentation B C (I.map (algebraMap A B)) κ)
      (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (hAB : (algebraMap A B).IsAdicHom)
      [RingHom.RigSmooth (algebraMap B C)],
      ∃ J : Ideal C, TopologicalRing.Ideal.IsIdealOfDefinition J ∧
        ∀ a ∈ J, ∀ x, homologyOneTensor I P Q x = 0 → a • x = 0)
