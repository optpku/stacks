/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.FundamentalClass
import Mathlib.Algebra.Algebra.Prod
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

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

namespace SchemeClassicalTheory

/-- The pair of cohomological pullbacks along two morphisms with a common codomain. -/
def pairedPullback
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} (i : X ⟶ Z) (j : Y ⟶ Z) : H Z →ₐ[F] H X × H Y :=
  (T.pullback i).toAlgHom.prod (T.pullback j).toAlgHom

/-- Evaluating `pairedPullback` restricts a class along each of the two morphisms. -/
@[simp]
theorem pairedPullback_apply
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} (i : X ⟶ Z) (j : Y ⟶ Z) (a : H Z) :
    T.pairedPullback i j a = (T.pullback i a, T.pullback j a) := sorry

/-- Restriction along the coprojections of a binary coproduct is bijective on total
cohomology for a scheme-classical theory. -/
theorem coproductPullback_bijective
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} (i : X ⟶ Z) (j : Y ⟶ Z)
    (e : IsColimit (BinaryCofan.mk i j)) :
    Function.Bijective (T.pairedPullback i j) := sorry

/-- A binary coproduct of nonempty equidimensional represented schemes of dimension `d`
is again nonempty and equidimensional of dimension `d`. -/
theorem coproduct_isNonemptyEquidimensional
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y d) (i : X ⟶ Z) (j : Y ⟶ Z)
    (e : IsColimit (BinaryCofan.mk i j)) :
    T.IsNonemptyEquidimensional Z d := sorry

/-- Integration on a binary coproduct is the sum of integration on its two
nonempty equidimensional components after pullback along the coprojections. -/
theorem integral_coproduct
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y d) (i : X ⟶ Z) (j : Y ⟶ Z)
    (e : IsColimit (BinaryCofan.mk i j)) :
    T.integral (T.coproduct_isNonemptyEquidimensional hX hY i j e) =
      (T.integral hX).comp (T.pullback i).toLinearMap +
        (T.integral hY).comp (T.pullback j).toLinearMap := sorry

/-- Pointwise form of integration on a binary coproduct. -/
theorem integral_coproduct_apply
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y Z : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y d) (i : X ⟶ Z) (j : Y ⟶ Z)
    (e : IsColimit (BinaryCofan.mk i j)) (a : H Z) :
    T.integral (T.coproduct_isNonemptyEquidimensional hX hY i j e) a =
      T.integral hX (T.pullback i a) + T.integral hY (T.pullback j a) := sorry

end SchemeClassicalTheory

end WeilCohomology
