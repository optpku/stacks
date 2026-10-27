/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Pushforward
import stacks_project.Chap77.Situation_77_12_1_FormalSystem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Situation 77.12.1: `A_lim` realizes `A = lim Aₙ`, the transition maps of `A`
are surjective with locally nilpotent kernels, and `toBase X` is separated
and of finite presentation. Each `Xn n` is the pullback of `X` to
`stageSpec A_lim n` and is a closed subspace of `X`. The finitely presented
modules `ℱ n` are flat and have proper support over `stageSpec A_lim n`;
pulling back `ℱ (n + 1)` to `Xn n` along `i n` gives the isomorphism `φ n` to
`ℱ n`. -/
@[stacks 0CX4] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.of :
    (A : SequentialInverseSystem CommRingCat.{u}) →
    (A_lim : LimitCone A) →
    A.Surjective →
    A.KernelLocallyNilpotent →
    (X : AlgebraicSpace (Spec A_lim.cone.pt)) →
    [Separated (toBase X)] →
    [FinitePresentation (toBase X)] →
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)) →
    (p : ∀ n, Xn n ⟶ X) →
    (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n) →
    (∀ n, IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X)) →
    [∀ n, IsClosedImmersion (p n)] →
    (i : ∀ n, Xn n ⟶ Xn (n + 1)) →
    (∀ n, i n ≫ p (n + 1) = p n) →
    (∀ n, i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n) →
    (ℱ : ∀ n, (Xn n).Modules) →
    [∀ n, (ℱ n).IsFinitePresentation] →
    (∀ n x, Modules.flatOverAt (ℱ n) (q n) x) →
    [∀ n, Modules.HasProperSupportOver (q n) (ℱ n)] →
    (φ : ∀ n,
      (Modules.pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n) →
    [∀ n, IsIso (φ n)] →
    AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem)
