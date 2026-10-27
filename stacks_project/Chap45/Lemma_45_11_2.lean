/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.SeparatingClosedPoints
import StacksCheckRecall

@[expose] public section

universe u v w x y z

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
variable (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
  fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward)

/- Lemma 45.11.2
existence of finitely many separable closed points jointly injecting H^0 is
equivalent to bijective degree-zero pullback from a representative of Spec Γ(X). -/
@[stacks 0FI0] #check
  (WeilCohomology.SchemeClassicalTheory.hasSeparatingClosedPoints_iff_globalSectionsPullback_bijective :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V] {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H : V → Type x} {CH : V → Type y}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
      {Hgrade : ∀ X, ℤ → Submodule F (H X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
        fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {K X : V} (s : X ⟶ K)
      (eK : T.scheme.obj K ≅
        Over.mk (Scheme.Hom.globalSectionsSpecMap (T.scheme.obj X).hom))
      (hs : (T.scheme.map s ≫ eK.hom).left = (T.scheme.obj X).left.toSpecΓ),
      T.HasSeparatingClosedPoints X ↔ Function.Bijective (T.degreeZeroPullback s))

#check
  (WeilCohomology.SchemeClassicalTheory.degreeZeroFiniteSeparable_of_hasSeparatingClosedPoints :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V] {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H : V → Type x} {CH : V → Type y}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
      {Hgrade : ∀ X, ℤ → Submodule F (H X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
        fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} (_hX : T.HasSeparatingClosedPoints X),
      Module.Finite F (Hgrade X (0)) ∧
        @Algebra.IsSeparable F (Hgrade X (0)) inferInstance
          (T.degreeZeroCommRing X).toRing inferInstance)

#check
  (WeilCohomology.SchemeClassicalTheory.hasSeparatingClosedPoints_iff_closedPointClasses_span_eq_top :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V] {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {H : V → Type x} {CH : V → Type y}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
      {Hgrade : ∀ X, ℤ → Submodule F (H X)}
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
      [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      (T : WeilCohomology.SchemeClassicalTheory k F TateLine V dimension product
        fst snd point H CH Hgrade CHgrade cyclePullback cyclePushforward)
      {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d),
      T.HasSeparatingClosedPoints X ↔
        @Submodule.span (Hgrade X (0)) (Hgrade X (2 * (d : ℤ)))
          (T.degreeZeroCommRing X).toSemiring _
          (WeilCohomology.SchemeClassicalTheory.moduleHgrade_of_degreeZero X
            (2 * (d : ℤ)))
          (Set.range (fun p : closedPoints (T.scheme.obj X).left ↦
            T.gradedCycleClass X (d : ℤ) (T.closedPointClass hX p))) = ⊤)
