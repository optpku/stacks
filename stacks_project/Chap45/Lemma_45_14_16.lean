/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.CycleClassPushforward

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

/- Lemma 45.14.16: Assume given data (D0), (D1), and (D2') satisfying axioms
/- 抽象层对角类 mixin：待 RL-2194 完成锚定后移除。 -/
(A1)–(A8). Then the cycle class map γ commutes with pushforward. -/
@[stacks 0FIT] #check
  (WeilCohomology.SchemePreWeilTheory.cycleClass_pushforward_of_axiomsA1ToA8 :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V]
      {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      {pointCycle : CHgrade point 0} {H Picard : V → Type x}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
      (T : WeilCohomology.SchemePreWeilTheory k F TateLine V dimension product fst snd
        point CH CHgrade cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
      (hA8 : T.SatisfiesAxiomA8) {X Y : V} {d e : ℕ}
      (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X),
      T.cycleClass Y (cyclePushforward f alpha) =
        T.pushforward hX hY f (T.cycleClass X alpha))
