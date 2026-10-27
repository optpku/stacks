/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace SchemeClassicalTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- Total cohomology of an empty represented scheme is zero. -/
theorem cohomology_eq_zero_of_isEmpty
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) [IsEmpty (T.scheme.obj X).left]
    (a : H X) :
    a = 0 := sorry

/-- The fundamental codimension-zero cycle class of a nonempty represented scheme is one. -/
theorem fundamentalCycleClass_eq_one
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) [Nonempty (T.scheme.obj X).left] :
    T.cycleClass X (1 : CHgrade X 0) = 1 := sorry

/-- The bidegree-zero cohomological unit of a nonempty represented scheme is nonzero. -/
theorem degreeZero_one_ne_zero
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    (X : V) [Nonempty (T.scheme.obj X).left] :
    (1 : Hgrade X (0)) ≠ 0 := sorry

end SchemeClassicalTheory

end WeilCohomology
