/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap45.Lemma_45_9_6
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Diagonal
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

universe u v w x y z

namespace WeilCohomology

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

/- Lemma 45.9.7: if the cycle class of the diagonal has Künneth decomposition
`∑ i, ∑ j, e i j ⊗ₜ[F] e' i j`, where each `e i` is a basis of `H^i(X)`, then
`∫_X e i j ∪ e' i j'` is `(-1) ^ i` times the Kronecker delta. -/
@[stacks 0FHH] #check
  (WeilCohomology.SchemeClassicalTheory.integral_basis_mul_diagonalComponent :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (diagonal : X ⟶ product X X)
      (diagonal_fst : diagonal ≫ fst X X = 𝟙 X)
      (diagonal_snd : diagonal ≫ snd X X = 𝟙 X)
      (β : Fin (2 * d + 1) → ℕ)
      (e : ∀ i, Module.Basis (Fin (β i)) F (Hgrade X ((i : ℤ))))
      (e' : ∀ i, Fin (β i) → Hgrade X (2 * (d : ℤ) - (i : ℤ)))
      (decomposition : T.kunnethMap X X
        (∑ i, ∑ j, (e i j : H X) ⊗ₜ[F] (e' i j : H X)) =
          T.cycleClass (product X X)
            (cyclePushforward diagonal (1 : CHgrade X 0))),
      ∀ (i) (j j' : Fin (β i)),
        T.integral hX ((e i j : H X) * (e' i j' : H X)) =
          if j = j' then (-1 : F) ^ (i : ℕ) else 0)

end WeilCohomology
