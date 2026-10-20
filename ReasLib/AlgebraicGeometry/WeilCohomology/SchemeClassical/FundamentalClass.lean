/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Nontriviality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

namespace SchemeClassicalTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- The cycle class of a pushed-forward fundamental cycle has the bidegree
prescribed by the difference of dimensions. -/
theorem cycleClass_pushforward_one_mem
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (i : X ⟶ Y) :
    T.cycleClass Y (cyclePushforward i (1 : CHgrade X 0)) ∈
      Hgrade Y (2 * ((e : ℤ) - d), (e : ℤ) - d) := sorry

/-- For a closed immersion of nonempty equidimensional represented schemes, the cycle
class of the pushed-forward fundamental cycle is the cohomological pushforward of one. -/
theorem fundamentalCycleClass_eq_pushforward_one
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (i : X ⟶ Y)
    [IsClosedImmersion (T.scheme.map i).left] :
    T.cycleClass Y (cyclePushforward i (1 : CHgrade X 0)) =
      T.pushforward hX hY i (1 : Hgrade X (0, 0)) := sorry

end SchemeClassicalTheory

end WeilCohomology
