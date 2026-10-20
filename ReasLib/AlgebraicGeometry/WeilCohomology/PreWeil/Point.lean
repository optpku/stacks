/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil

@[expose] public section

universe u v w x y z

open CategoryTheory

namespace WeilCohomology.SchemePreWeilTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type x}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

/-- The distinguished object representing `Spec(k)` is nonempty equidimensional
of dimension zero. -/
theorem point_isNonemptyEquidimensional :
    T.IsNonemptyEquidimensional point 0 := sorry

/-- The cycle class of the fundamental degree-zero cycle on the distinguished point
is the cohomological unit. -/
theorem pointFundamentalCycleClass_eq_one :
    T.cycleClass point (1 : CHgrade point 0) = 1 := sorry

/-- Integration on the distinguished point sends the cohomological unit to the
coefficient-field unit. -/
theorem pointIntegral_one :
    T.integral T.point_isNonemptyEquidimensional 1 = 1 := sorry

/-- The cycle class of the fundamental degree-zero cycle on the distinguished point
has normalized integral. -/
theorem point_normalization :
    T.integral T.point_isNonemptyEquidimensional
      (T.cycleClass point (1 : CHgrade point 0)) = 1 := sorry

end WeilCohomology.SchemePreWeilTheory
