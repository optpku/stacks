module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Derived module systems on a formal completion of an algebraic space

This module bundles compatible pseudo-coherent derived modules on the base-change
stages of an algebraic space over the limit of a sequential inverse system of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

/-- A compatible system of pseudo-coherent derived modules on the base-change
stages of an algebraic space over the limit of a sequential inverse system of
rings. The stored successor maps are derived-pullback isomorphisms
`(modulePullbackDerived (i n)).obj (K (n + 1)) ≅ K n`; these are the adjoints of
the source maps `K (n + 1) ⟶ R(i n)_* (K n)` in `D(𝒪_{X_{n+1}})`. -/
structure System
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt))
    (p : ∀ n, Xn n ⟶ X) (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)] where
  /-- Every successor transition of the ring system is surjective. -/
  surjective : A.Surjective
  /-- Every successor transition of the ring system has locally nilpotent kernel. -/
  kernelLocallyNilpotent : A.KernelLocallyNilpotent
  /-- Each stage is the base change of the ambient algebraic space to the corresponding ring. -/
  isPullback : ∀ n,
    IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X)
  /-- Each stage maps to the ambient algebraic space by a closed immersion. -/
  isClosedImmersion : ∀ n, IsClosedImmersion (p n)
  /-- Successor maps of stages commute with the maps to the ambient algebraic space. -/
  comp_p : ∀ n, i n ≫ p (n + 1) = p n
  /-- Successor maps of stages commute with the maps to the rings in the inverse system. -/
  comp_q : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n
  /-- The derived module at each base-change stage. -/
  K : ∀ n, ModuleDerived (Xn n)
  /-- Every derived module in the system is pseudo-coherent. -/
  isPseudoCoherent : ∀ n, IsPseudoCoherent (Xn n) (K n)
  /-- The derived-pullback isomorphism identifying the next stage with the current one. -/
  transitionIso :
    ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ≅ K n

namespace System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

/-- Construct a formal-completion system from its geometric stages, derived modules,
successor maps, and their compatibility properties. -/
def of
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (K : ∀ n, ModuleDerived (Xn n))
    (hK : ∀ n, IsPseudoCoherent (Xn n) (K n))
    (φ : ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ⟶ K n)
    [∀ n, IsClosedImmersion (p n)] [∀ n, IsIso (φ n)] :
    System A A_lim X Xn p q i where
  surjective := h_surjective
  kernelLocallyNilpotent := h_kernel
  isPullback := h_pullback
  isClosedImmersion := fun _ ↦ inferInstance
  comp_p := hiX
  comp_q := hiA
  K := K
  isPseudoCoherent := hK
  transitionIso := fun n ↦ asIso (φ n)

/-- The constructed formal-completion system has the supplied derived modules and
derived-pullback transitions, and satisfies the supplied geometric, ring, and
pseudo-coherence conditions. -/
theorem of_spec
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (K : ∀ n, ModuleDerived (Xn n))
    (hK : ∀ n, IsPseudoCoherent (Xn n) (K n))
    (φ : ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ⟶ K n)
    [∀ n, IsClosedImmersion (p n)] [∀ n, IsIso (φ n)] :
    let S := of h_surjective h_kernel h_pullback hiX hiA K hK φ
    S.K = K ∧
      (∀ n, (S.transitionIso n).hom = φ n) ∧
      A.Surjective ∧ A.KernelLocallyNilpotent ∧
      (∀ n, IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X)) ∧
      (∀ n, IsClosedImmersion (p n)) ∧
      (∀ n, i n ≫ p (n + 1) = p n) ∧
      (∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n) ∧
      (∀ n, IsPseudoCoherent (Xn n) (K n)) := sorry

/-- The finite-stage algebraic space `X_n` viewed as a closed subspace of `X`. -/
def stageClosedSubspace (S : System A A_lim X Xn p q i) (n : ℕ) : ClosedSubspace X where
  X := Xn n
  ι := p n
  isClosedImmersion := S.isClosedImmersion n

end System

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion
