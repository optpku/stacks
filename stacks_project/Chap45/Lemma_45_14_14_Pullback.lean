/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace WeilCohomology.PreWeilTheory

/-! Compatibility surface for the promoted homogeneous pullback. -/
#check (pullbackGrade :
  ∀ {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V}
    (f : X ⟶ Y) (p : ℤ), T.Hgrade Y p →ₗ[F] T.Hgrade X p)
#check (pullbackGrade_apply :
  ∀ {F : Type u} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type v} [Category.{v} V] {H Picard Cycle : V → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine V H Picard Cycle) {X Y : V}
    (f : X ⟶ Y) (p : ℤ) (a : T.Hgrade Y p),
    T.pullback f a = T.pullbackGrade f p a)

end WeilCohomology.PreWeilTheory
