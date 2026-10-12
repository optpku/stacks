/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.ZeroCycles
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.DimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.RingTheory.Trace.AlgHom

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

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd pt
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

namespace ZeroCycles

/-- For an equidimensional represented scheme over a nonempty
zero-dimensional represented base, distinct cycle classes of two sections make
their point-class difference indivisible by every integer greater than one. -/
theorem pointSub_not_divisible_of_cycleClass_ne_of_equidimensional
    {K X : V} {d : ℕ} (hK : T.IsNonemptyEquidimensional K 0)
    (hX : T.IsNonemptyEquidimensional X d) (p : X ⟶ K)
    (x x' : K ⟶ X) (hx : x ≫ p = 𝟙 K) (hx' : x' ≫ p = 𝟙 K)
    (hcycle : T.cycleClass X (pointClass T x) ≠
      T.cycleClass X (pointClass T x'))
    (n : ℤ) (hn : 1 < n) :
    ¬ ∃ z : T.zeroCycles X,
      pointClass T x - pointClass T x' = n • (z : CH X) := sorry

/-- Let `k'/k` be a finite separable field extension and let a represented
scheme be smooth and projective over the represented spectrum of `k'`. If two
sections have distinct cycle classes, then their point-class difference is not
divisible by any integer greater than one. -/
theorem pointSub_not_divisible_of_cycleClass_ne
    {k' : Type u} [Field k'] [Algebra k k'] [Module.Finite k k']
    [Algebra.IsSeparable k k'] {K X : V} (p : X ⟶ K)
    (eK : T.scheme.obj K ≅ Over.mk (Scheme.AffineBaseChange.specMap k k'))
    [Smooth (T.scheme.map p ≫ eK.hom).left]
    [Projective (T.scheme.map p ≫ eK.hom).left]
    (x x' : K ⟶ X) (hx : x ≫ p = 𝟙 K) (hx' : x' ≫ p = 𝟙 K)
    (hcycle : T.cycleClass X (pointClass T x) ≠
      T.cycleClass X (pointClass T x'))
    (n : ℤ) (hn : 1 < n) :
    ¬ ∃ z : T.zeroCycles X,
      pointClass T x - pointClass T x' = n • (z : CH X) := sorry

end ZeroCycles

end WeilCohomology.SchemeClassicalTheory
