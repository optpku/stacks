/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion

/-!
# Derived module systems on a formal completion of an algebraic space

Typed compatibility checks for compatible pseudo-coherent derived modules and their
closed base-change stages.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System :
  ∀
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt))
    (p : ∀ n, Xn n ⟶ X) (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.of :
  ∀
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : AlgebraicSpace (Spec A_lim.cone.pt)}
    {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
    {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)]
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (SchemeRealization.toBase X))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (K : ∀ n, ModuleDerived (Xn n))
    (hK : ∀ n, IsPseudoCoherent (Xn n) (K n))
    (φ : ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ⟶ K n)
    [∀ n, IsClosedImmersion (p n)] [∀ n, IsIso (φ n)],
    System A A_lim X Xn p q i)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.of_spec :
  ∀
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : AlgebraicSpace (Spec A_lim.cone.pt)}
    {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
    {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)]
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (SchemeRealization.toBase X))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)
    (K : ∀ n, ModuleDerived (Xn n))
    (hK : ∀ n, IsPseudoCoherent (Xn n) (K n))
    (φ : ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ⟶ K n)
    [∀ n, IsClosedImmersion (p n)] [∀ n, IsIso (φ n)],
    let S := System.of h_surjective h_kernel h_pullback hiX hiA K hK φ
    S.K = K ∧
      (∀ n, (S.transitionIso n).hom = φ n) ∧
      A.Surjective ∧ A.KernelLocallyNilpotent ∧
      (∀ n, IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (SchemeRealization.toBase X)) ∧
      (∀ n, IsClosedImmersion (p n)) ∧
      (∀ n, i n ≫ p (n + 1) = p n) ∧
      (∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n) ∧
      (∀ n, IsPseudoCoherent (Xn n) (K n)))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.stageClosedSubspace :
  ∀
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : AlgebraicSpace (Spec A_lim.cone.pt)}
    {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
    {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)]
    (S : System A A_lim X Xn p q i) (n : ℕ), ClosedSubspace X)
