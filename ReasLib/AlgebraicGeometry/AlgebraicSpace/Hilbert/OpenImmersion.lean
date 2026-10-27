/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# The Hilbert functor map along an open immersion

An open immersion `π : X ⟶ Y` of algebraic spaces over `B` induces a comparison
`X_T ⟶ Y_T` on fibres and a natural transformation `hilbert (π ≫ y) ⟶ hilbert y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (fiber)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `π : X ⟶ Y` over `B`. -/
def fiberComparison (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B) :
    fiber (π ≫ y) σ ⟶ fiber y σ :=
  pullback.map (π ≫ y) σ.hom y σ.hom π
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (π ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison of an open immersion is an open immersion. -/
instance instIsOpenImmersion_fiberComparison (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) [IsOpenImmersion π] :
    IsOpenImmersion (fiberComparison π y σ) :=
  sorry

/-- The fibre comparison is an open immersion, and the square to `X ⟶ Y` commutes. -/
theorem fiberComparison_spec (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B)
    [IsOpenImmersion π] :
    IsOpenImmersion (fiberComparison π y σ) ∧
      fiberComparison π y σ ≫ pullback.fst y σ.hom =
        pullback.fst (π ≫ y) σ.hom ≫ π :=
  sorry

namespace Point

/-- Composing the inclusion of a Hilbert point with the fibre comparison gives a
closed immersion whose structure morphism is of finite presentation, flat, and proper. -/
theorem pushforward_properties (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    IsClosedImmersion (p.subspace.ι ≫ fiberComparison π y σ) ∧
      FinitePresentation
        ((p.subspace.ι ≫ fiberComparison π y σ) ≫ pullback.snd y σ.hom) ∧
      Flat ((p.subspace.ι ≫ fiberComparison π y σ) ≫ pullback.snd y σ.hom) ∧
      Proper ((p.subspace.ι ≫ fiberComparison π y σ) ≫ pullback.snd y σ.hom) :=
  sorry

/-- View a Hilbert point of `X_T` as a Hilbert point of `Y_T` along `π`,
using that `y : Y ⟶ B` is separated. -/
def pushforward (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) : Point y σ where
  subspace :=
    { X := p.subspace.X
      ι := p.subspace.ι ≫ fiberComparison π y σ
      isClosedImmersion := (pushforward_properties π y p).1 }
  isFinitePresentation := (pushforward_properties π y p).2.1
  isFlat := (pushforward_properties π y p).2.2.1
  isProper := (pushforward_properties π y p).2.2.2

/-- The inclusion of a pushed Hilbert point is the original inclusion composed
with the fibre comparison, using that `y` is separated. -/
theorem pushforward_ι (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    (pushforward π y p).subspace.ι = p.subspace.ι ≫ fiberComparison π y σ :=
  sorry

/-- A pushed Hilbert point remains a closed subspace of `Y_T` whose structure
map to `T` is of finite presentation, flat, and proper, using that `y` is
separated. -/
theorem pushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    IsClosedImmersion (pushforward π y p).subspace.ι ∧
      FinitePresentation (pushforward π y p).structureMap ∧
      Flat (pushforward π y p).structureMap ∧
      Proper (pushforward π y p).structureMap :=
  sorry

end Point

/-- Pushforward of Hilbert points preserves ideal-sheaf identification, using
that `y` is separated. -/
theorem Rel_pushforward (π : X ⟶ Y) (y : Y ⟶ B)
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : SchemeOver B) :
    ∀ (p q : Point (π ≫ y) σ),
      (setoid (π ≫ y) σ).r p q →
        (setoid y σ).r (Point.pushforward π y p) (Point.pushforward π y q) :=
  sorry

/-- The natural transformation `Hilb_{X/B} ⟶ Hilb_{Y/B}` induced by an open
immersion `π : X ⟶ Y` of algebraic spaces with `y : Y ⟶ B` separated. -/
def map (π : X ⟶ Y) (y : Y ⟶ B)
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    hilbert (π ≫ y) ⟶ hilbert y where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun p : Point (π ≫ y) σ.unop ↦ Point.pushforward π y p)
        (Rel_pushforward π y σ.unop))
  naturality := sorry

/-- The component of `map π y` at a scheme over `B` is the quotient map of
`Point.pushforward`, using that `y` is separated. -/
theorem map_app (π : X ⟶ Y) (y : Y ⟶ B)
    [IsOpenImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : (SchemeOver B)ᵒᵖ) :
    (map π y).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun p : Point (π ≫ y) σ.unop ↦ Point.pushforward π y p)
          (Rel_pushforward π y σ.unop)) :=
  sorry

/-- Scheme-level open immersions, as a morphism property on schemes over `B`. -/
def openImmersionSchemesOver : MorphismProperty (SchemeOver B) :=
  fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is an open
immersion when it is relatively representable with respect to `uliftYoneda` and
every represented pullback is an open immersion of schemes. -/
def IsOpenImmersionOnSchemesOver {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  openImmersionSchemesOver.relative uliftYoneda.{u + 1} φ

/-- Open immersions of Hilbert-sized functors are relatively representable
`uliftYoneda` morphisms whose represented scheme maps are open immersions. -/
theorem isOpenImmersionOnSchemesOver_iff {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsOpenImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsOpenImmersion snd.left.left :=
  sorry

/-- If `π : X ⟶ Y` is an open immersion of algebraic spaces which
are separated and of finite presentation over an algebraic space `B`, then `π`
induces an open immersion `map π y : hilbert (π ≫ y) ⟶ hilbert y`. -/
@[stacks 0DPE]
theorem isOpenImmersion_map {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (π : X ⟶ Y) (y : Y ⟶ B) [IsOpenImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    IsOpenImmersionOnSchemesOver (map π y) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hilbert
