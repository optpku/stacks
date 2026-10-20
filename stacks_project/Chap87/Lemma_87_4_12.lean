module

public import ReasLib.Topology.Algebra.TensorProduct.Admissibility
import StacksCheckRecall

@[expose] public section

open Algebra.TensorProduct
open scoped Topology

universe u

/- Lemma 87.4.12 (1): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are weakly pre-admissible, then
A ⊗̂_B C is weakly admissible. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isWeaklyAdmissibleRing :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadmissibleRing A]
    [TopologicalRing.IsWeaklyPreadmissibleRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)),
    TopologicalRing.IsWeaklyAdmissibleRing (Completed B A C))

/- Lemma 87.4.12 (2): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are pre-admissible, then
A ⊗̂_B C is admissible. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isAdmissibleRing :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsPreadmissibleRing A] [TopologicalRing.IsPreadmissibleRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)),
    TopologicalRing.IsAdmissibleRing (Completed B A C))

/- Lemma 87.4.12 (3): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C have a countable fundamental system
of open ideals, then A ⊗̂_B C has a countable fundamental system of open
ideals. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isCountablyGenerated_nhds :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [IsTopologicalRing A] [IsLinearTopology A A]
    [IsTopologicalRing C] [IsLinearTopology C C]
    [(nhds (0 : A)).IsCountablyGenerated] [(nhds (0 : C)).IsCountablyGenerated]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)),
    (nhds (0 : Completed B A C)).IsCountablyGenerated)

/- Lemma 87.4.12 (4): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are pre-adic with finitely generated
ideals of definition, then A ⊗̂_B C is adic and has a finitely generated
ideal of definition. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isAdicWithFGIdealOfDefinition :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsPreadicRing A] [TopologicalRing.IsPreadicRing C]
    [IsLinearTopology A A] [IsLinearTopology C C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C))
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hCfg : ∃ J : Ideal C, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J),
    TopologicalRing.IsAdicRing (Completed B A C) ∧
      ∃ K : Ideal (Completed B A C),
        K.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition K)

/- Lemma 87.4.12 (5): If B → A and B → C are continuous homomorphisms of
linearly topologized rings, A and C are pre-adic Noetherian rings, and
B ⧸ topologicalNilradical B →+* A ⧸ topologicalNilradical A is of finite
type, then A ⊗̂_B C is adic Noetherian. -/
@[stacks 0GB4] #check (Algebra.TensorProduct.Completed.isAdicNoetherianRing :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsPreadicRing A] [TopologicalRing.IsPreadicRing C]
    [IsLinearTopology A A] [IsLinearTopology C C]
    [IsNoetherianRing A] [IsNoetherianRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C))
    (hfin : (topologicalNilradical.quotientMap (algebraMap B A) hA).FiniteType),
    TopologicalRing.IsAdicRing (Completed B A C) ∧
      IsNoetherianRing (Completed B A C))
