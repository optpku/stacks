/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.DimensionZero

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology.SchemeClassicalTheory

open CategoryTheory

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

/- Degree-zero commutative-ring compatibility API. -/
#check
  (WeilCohomology.SchemeClassicalTheory.degreeZero_mul_comm :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V) (a b : Hgrade X (0, 0)), a * b = b * a)

#check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroCommRing :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V), CommRing (Hgrade X (0, 0)))

#check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroCommRing_toRing :
    ∀ (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
        H CH Hgrade CHgrade cyclePullback cyclePushforward)
      (X : V),
      (T.degreeZeroCommRing X).toRing =
        (inferInstance : Ring (Hgrade X (0, 0))))

end WeilCohomology.SchemeClassicalTheory

