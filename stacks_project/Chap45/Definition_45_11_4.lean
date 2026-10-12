/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.IsWeil

universe u v w x y z

open AlgebraicGeometry CategoryTheory

/- Definition 45.11.4: a Weil cohomology theory over a field `k` with
characteristic-zero coefficients in `F` is a scheme-valued classical theory
satisfying the equivalent conditions of Lemma 45.11.2 for every represented
smooth projective scheme. -/
@[stacks 0FI2] #check (WeilCohomology.SchemeClassicalTheory.IsWeil :
  {k : Type u} → [Field k] → {F : Type v} → [Field F] → [CharZero F] →
  {TateLine : Type w} → [AddCommGroup TateLine] → [Module F TateLine] →
  {V : Type w} → [Category.{z} V] →
  {dimension : V → ℕ} → {product : V → V → V} →
  {fst : ∀ X Y, product X Y ⟶ X} → {snd : ∀ X Y, product X Y ⟶ Y} →
  {point : V} → {H : V → Type x} → {CH : V → Type y} →
  [∀ X, Ring (H X)] → [∀ X, Algebra F (H X)] → [∀ X, CommRing (CH X)] →
  {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)} →
  {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} →
  [∀ X, GradedAlgebra (Hgrade X)] → [∀ X, GradedAlgebra (CHgrade X)] →
  {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X} →
  {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y} →
  WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product fst snd
    point H CH Hgrade CHgrade cyclePullback cyclePushforward → Prop)
