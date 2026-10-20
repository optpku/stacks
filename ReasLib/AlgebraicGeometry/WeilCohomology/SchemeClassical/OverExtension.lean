/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Represented schemes over a field extension

This module records the represented scheme over `k'` obtained from a morphism to a
represented spectrum of a field extension of `k`.
-/

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
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- A represented scheme over `k`, equipped with its induced structure morphism over
the extension field `k'`. -/
noncomputable def overExtension
    {k' : Type u} [Field k'] [Algebra k k'] {K X : V} (s : X ⟶ K)
    (eK : T.scheme.obj K ≅
      Over.mk (Scheme.AffineBaseChange.specMap k k')) :
    SchemeOverField k' :=
  Over.mk ((T.scheme.map s ≫ eK.hom).left)

/-- The structure morphism of `overExtension` is the represented map to `K`,
followed by the chosen identification of `K` with `Spec(k')`. -/
theorem overExtension_hom
    {k' : Type u} [Field k'] [Algebra k k'] {K X : V} (s : X ⟶ K)
    (eK : T.scheme.obj K ≅
      Over.mk (Scheme.AffineBaseChange.specMap k k')) :
    (T.overExtension s eK).hom = (T.scheme.map s ≫ eK.hom).left := sorry

end WeilCohomology.SchemeClassicalTheory
