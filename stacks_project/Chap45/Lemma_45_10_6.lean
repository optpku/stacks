/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.ZeroCycles.Nondivisibility
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {pt : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/- Lemma 45.10.6: for a finite separable extension `k'/k`, a smooth projective
represented `k'`-scheme, and two `k'`-rational points with distinct cycle
classes, their zero-cycle difference is not divisible by any integer greater
than one. -/
@[stacks 0FHU] #check
  (WeilCohomology.SchemeClassicalTheory.ZeroCycles.pointSub_not_divisible_of_cycleClass_ne :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd pt
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {k' : Type u} [Field k'] [Algebra k k'] [Module.Finite k k']
      [Algebra.IsSeparable k k'] {K X : V} (p : X ⟶ K)
      (eK : T.scheme.obj K ≅ Over.mk (Scheme.AffineBaseChange.specMap k k'))
      [Smooth (T.scheme.map p ≫ eK.hom).left]
      [Projective (T.scheme.map p ≫ eK.hom).left]
      (x x' : K ⟶ X) (hx : x ≫ p = 𝟙 K) (hx' : x' ≫ p = 𝟙 K)
      (hcycle : T.cycleClass X (ZeroCycles.pointClass T x) ≠
        T.cycleClass X (ZeroCycles.pointClass T x'))
      (n : ℤ) (hn : 1 < n),
      ¬ ∃ z : T.zeroCycles X,
        ZeroCycles.pointClass T x - ZeroCycles.pointClass T x' =
          n • (z : CH X))

end WeilCohomology.SchemeClassicalTheory
