/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.PoincareDuality
import StacksCheckRecall

@[expose] public section

universe u v w x y z

open CategoryTheory

/- Lemma 45.14.5 -/
@[stacks 0FIJ] #check
  (WeilCohomology.SchemePreWeilTheory.poincareDuality_of_axiomsA1ToA7 :
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
        CH CHgrade cyclePullback cyclePushforward pointCycle H Picard),
      (∀ {X d}, T.IsNonemptyEquidimensional X d → ∀ p : ℤ × ℤ,
        Module.Finite F (T.Hgrade X p)) ∧
      (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ)
        (a : T.Hgrade X (2 * (d : ℤ) - i, (d : ℤ) - j))
        (b : T.Hgrade X (i, j)),
        T.poincarePairing hX i j a b = T.integral hX (b * a)) ∧
      (∀ {X d} (hX : T.IsNonemptyEquidimensional X d) (i j : ℤ),
        Function.Bijective (T.poincarePairing hX i j)))
