module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_3_0_1»

public import ReasLib.RingTheory.AdicCompletion.RigEtale

/-!
# Rig-étale algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-étale when it is
topologically of finite type and some power of `I` annihilates the homology of
the completed naive cotangent complex `NL_{B/A}^∧` in degrees `1` and `0`. A
continuous homomorphism of adic Noetherian topological rings is rig-étale when
this holds for some, equivalently any, ideal of definition of `A` that also
induces the ambient topology on `B`.
-/

@[expose] public section

universe u

#check (RingHom.RigEtale :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)
