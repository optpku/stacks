/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap45.Lemma_45_9_9
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open CategoryTheory CategoryTheory.Limits

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
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/- Lemma 45.10.1: integration on a binary coproduct is the sum of integration on its
two nonempty equidimensional components after pullback along the coprojections. -/
@[stacks 0FHP] #check
  (WeilCohomology.SchemeClassicalTheory.integral_coproduct :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X Y Z : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y d) (i : X ⟶ Z) (j : Y ⟶ Z)
      (e : IsColimit (BinaryCofan.mk i j)),
      T.integral (T.coproduct_isNonemptyEquidimensional hX hY i j e) =
        (T.integral hX).comp (T.pullback i).toLinearMap +
          (T.integral hY).comp (T.pullback j).toLinearMap)

#check
  (WeilCohomology.SchemeClassicalTheory.integral_coproduct_apply :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X Y Z : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y d) (i : X ⟶ Z) (j : Y ⟶ Z)
      (e : IsColimit (BinaryCofan.mk i j)) (a : H Z),
      T.integral (T.coproduct_isNonemptyEquidimensional hX hY i j e) a =
        T.integral hX (T.pullback i a) + T.integral hY (T.pullback j a))

end WeilCohomology
