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

/- Remark 45.14.6 (Uniqueness of trace maps): for a SchemePreWeilTheory
satisfying data (D0), (D1), and (D2') with axioms (A1)--(A7), Poincare
duality makes normalized contraction against the diagonal tensor
nondegenerate. Thus every trace LinearMap `H X →ₗ[F] F` whose contraction
with that tensor is `1` equals the theory's integral trace, for each
nonempty equidimensional object `X` of dimension `d`. -/
@[stacks 0FIK] #check
  (WeilCohomology.SchemePreWeilTheory.axiomA6_unique :
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
        CH CHgrade cyclePullback cyclePushforward pointCycle H Picard)
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (trace : H X →ₗ[F] F),
      WeilCohomology.contractRight trace (T.diagonalTensor hX) = 1 → trace = T.integral hX)
