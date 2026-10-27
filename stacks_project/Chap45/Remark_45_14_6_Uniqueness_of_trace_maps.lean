/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil
import StacksCheckRecall

open CategoryTheory

universe u v w x y z

/- Remark 45.14.6: axioms (A1)--(A7) uniquely determine the normalized
/- 抽象层对角类 mixin：待 RL-2194 完成锚定后移除。 -/
trace on H^{2d}(X)(d). The contraction uses its canonical zero extension. -/
@[stacks 0FIK] #check
  (WeilCohomology.SchemePreWeilTheory.sourceAxiomA6_unique :
    ∀ {k : Type u} [Field k]
      {F : Type v} [Field F] [CharZero F]
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
      (T : WeilCohomology.SchemePreWeilTheory k F TateLine V dimension product fst snd point
        CH CHgrade cyclePullback cyclePushforward pointCycle H Picard) [T.HasDiagonalClassRelation]
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (trace : T.twistedGrade X (2 * (d : ℤ)) d →ₗ[F] F),
      WeilCohomology.contractTwistedRight
          (WeilCohomology.extendTopTrace (T.Hgrade X) (T.Hgrade_isInternal X) d trace)
          (T.twistedDiagonalTensor hX) = 1 → trace = T.twistedTopIntegral hX)
