/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.BaseChange

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

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
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

#check (WeilCohomology.SchemeClassicalTheory.degreeZeroPullback :
  ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
    H CH Hgrade CHgrade cyclePullback cyclePushforward) {X Y : V} (f : X ⟶ Y),
    Hgrade Y (0) →+* Hgrade X (0))

#check (WeilCohomology.SchemeClassicalTheory.degreeZeroAction :
  ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
    H CH Hgrade CHgrade cyclePullback cyclePushforward) {X S : V} (f : X ⟶ S),
    Hgrade S (0) →+* H X)

end WeilCohomology.SchemeClassicalTheory
