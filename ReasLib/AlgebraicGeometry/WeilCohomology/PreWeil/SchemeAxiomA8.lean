/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections
public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

/-- A scheme-valued pre-Weil theory satisfies Axiom A8 when degree-`0`
pullback is bijective along every represented canonical morphism to the
spectrum of global sections. -/
def SatisfiesAxiomA8
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
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
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) : Prop :=
  ∀ (X G : V) (g : X ⟶ G)
    (eG : T.scheme.obj G ≅ SchemeOverField.globalSectionsSpec (T.scheme.obj X)),
    (T.scheme.map g).left =
        (SchemeOverField.toGlobalSectionsSpec (T.scheme.obj X)).left ≫ eG.inv.left →
      Function.Bijective (T.pullbackGrade g 0)

/-- Axiom A8 unfolds to bijectivity of degree-`0` pullback along every
represented global-sections morphism. -/
theorem satisfiesAxiomA8_iff
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
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
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) :
    T.SatisfiesAxiomA8 ↔
      ∀ (X G : V) (g : X ⟶ G)
        (eG : T.scheme.obj G ≅ SchemeOverField.globalSectionsSpec (T.scheme.obj X)),
        (T.scheme.map g).left =
            (SchemeOverField.toGlobalSectionsSpec (T.scheme.obj X)).left ≫ eG.inv.left →
          Function.Bijective (T.pullbackGrade g 0) := sorry

end WeilCohomology.SchemePreWeilTheory
