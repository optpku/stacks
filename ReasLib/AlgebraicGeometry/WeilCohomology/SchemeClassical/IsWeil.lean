/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.SeparatingClosedPoints

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
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V},
  (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

variable (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
  H CH Hgrade CHgrade cyclePullback cyclePushforward)

/-- A scheme-valued classical theory is Weil when every represented smooth
projective scheme has separating separable closed points. -/
def IsWeil : Prop :=
  ∀ X : V, T.HasSeparatingClosedPoints X

/-- The universal separating-closed-points characterization of `IsWeil`. -/
theorem isWeil_iff :
    T.IsWeil ↔ ∀ X : V, T.HasSeparatingClosedPoints X := sorry

namespace IsWeil

/-- A Weil theory has separating separable closed points on every represented
smooth projective scheme. -/
theorem hasSeparatingClosedPoints (hT : T.IsWeil) (X : V) :
    T.HasSeparatingClosedPoints X := sorry

/-- For a Weil theory, pullback from a representative of the spectrum of global
sections is bijective on degree-zero cohomology. -/
theorem globalSectionsPullback_bijective (hT : T.IsWeil)
    {K X : V} (s : X ⟶ K)
    (eK : T.scheme.obj K ≅
      Over.mk (Scheme.Hom.globalSectionsSpecMap (T.scheme.obj X).hom))
    (hs : (T.scheme.map s ≫ eK.hom).left = (T.scheme.obj X).left.toSpecΓ) :
    Function.Bijective (T.degreeZeroPullback s) := sorry

end IsWeil

end WeilCohomology.SchemeClassicalTheory
