/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

universe u

/- Situation 77.13.1: `A_lim` realizes `A = lim Aₙ`, the transition maps of `A`
are surjective with locally nilpotent kernels, and `SchemeRealization.toBase X` is proper, flat,
and of finite presentation. Each square defining `Xn n` is cartesian and
`p n : Xn n ⟶ X` is a closed immersion. The pseudo-coherent objects `K n` are
linked by derived-pullback isomorphisms `L(i n)^* K (n + 1) ≅ K n`. -/
@[stacks 0DIK] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.of :
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
