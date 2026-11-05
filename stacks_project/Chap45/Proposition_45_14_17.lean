/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.ToSchemeClassical

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w x y z

/- Proposition 45.14.17: Assume given data (D0), (D1), and (D2') satisfying
/- 抽象层对角类 mixin：待 RL-2194 完成锚定后移除。 -/
axioms (A1)–(A8). Then we have a Weil cohomology theory. -/
@[stacks 0FIU] #check
  (WeilCohomology.SchemePreWeilTheory.isWeil_of_axiomsA1ToA8 :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V]
      {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      {pointCycle : CHgrade point 0} {H Picard : V → Type w}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
      (T : WeilCohomology.SchemePreWeilTheory k F TateLine V dimension product fst snd
        point CH CHgrade cyclePullback cyclePushforward pointCycle H Picard)
      (C : @WeilCohomology.SchemeChowComparison k _ V _ T.scheme CH _ CHgrade
        T.IsNonemptyEquidimensional
        (fun X ↦ (T.projective X).isProper.toLocallyOfFiniteType))
      [T.HasDiagonalClassRelation]
      (hC : @WeilCohomology.SchemeChowComparison.RespectsOperations k _ V _
        T.scheme CH _ CHgrade _ T.IsNonemptyEquidimensional
        (fun X ↦ (T.projective X).isProper.toLocallyOfFiniteType)
        C cyclePullback cyclePushforward)
      (hA8 : T.SatisfiesAxiomA8),
      -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
      letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
      (T.toSchemeClassicalTheory C hC hA8).IsWeil)
