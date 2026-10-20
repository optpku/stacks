/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FiberComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# The Hilbert functor map along a closed immersion

A closed immersion `π : X ⟶ Y` of algebraic spaces over `B` induces a
comparison `X_T ⟶ Y_T` on fibres and a natural transformation
`hilbert (π ≫ y) ⟶ hilbert y`.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

namespace Point

-- The private proof is exported for use in the exposed constructor proof fields.
set_option backward.privateInPublic true in
/-- Composing the inclusion of a Hilbert point with the fibre comparison gives
a closed immersion whose structure map is of finite presentation, flat, and proper. -/
private theorem closedPushforward_properties (π : X ⟶ Y) (y : Y ⟶ B)
    {σ : SchemeOver B} [IsClosedImmersion π] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] (p : Point (π ≫ y) σ) :
    IsClosedImmersion (p.subspace.ι ≫ Quot.fiberComparison π y σ) ∧
      FinitePresentation
        ((p.subspace.ι ≫ Quot.fiberComparison π y σ) ≫ pullback.snd y σ.hom) ∧
      Flat ((p.subspace.ι ≫ Quot.fiberComparison π y σ) ≫ pullback.snd y σ.hom) ∧
      Proper ((p.subspace.ι ≫ Quot.fiberComparison π y σ) ≫ pullback.snd y σ.hom) := sorry

-- Exposing the carrier and inclusion requires access to the private property proof.
set_option backward.privateInPublic true in
/-- View a Hilbert point of `X_T` as a Hilbert point of `Y_T` along a closed
immersion `π`, using that `y : Y ⟶ B` is separated. -/
@[expose] def closedPushforward (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) : Point y σ where
  subspace :=
    { X := p.subspace.X
      ι := p.subspace.ι ≫ Quot.fiberComparison π y σ
      isClosedImmersion := (closedPushforward_properties π y p).1 }
  isFinitePresentation := (closedPushforward_properties π y p).2.1
  isFlat := (closedPushforward_properties π y p).2.2.1
  isProper := (closedPushforward_properties π y p).2.2.2

/-- The inclusion of a closed-pushed Hilbert point is the original inclusion
composed with the fibre comparison, using that `y` is separated. -/
theorem closedPushforward_ι (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    (closedPushforward π y p).subspace.ι =
      p.subspace.ι ≫ Quot.fiberComparison π y σ := sorry

/-- A closed-pushed Hilbert point remains a closed subspace of `Y_T` whose
structure map to `T` is of finite presentation, flat, and proper, using that
`y` is separated. -/
theorem closedPushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) {σ : SchemeOver B}
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (p : Point (π ≫ y) σ) :
    IsClosedImmersion (closedPushforward π y p).subspace.ι ∧
      FinitePresentation (closedPushforward π y p).structureMap ∧
      Flat (closedPushforward π y p).structureMap ∧
      Proper (closedPushforward π y p).structureMap := sorry

end Point

/-- Closed pushforward of Hilbert points preserves ideal-sheaf identification,
using that `y` is separated. -/
theorem Rel_closedPushforward (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : SchemeOver B) :
    ∀ (p q : Point (π ≫ y) σ),
      (setoid (π ≫ y) σ).r p q →
        (setoid y σ).r (Point.closedPushforward π y p)
          (Point.closedPushforward π y q) := sorry

/-- The quotient maps induced by closed pushforward commute with pullback
along morphisms of test schemes. -/
theorem closedMap_naturality (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (hilbert (π ≫ y)).map h ≫
        TypeCat.ofHom
          (_root_.Quotient.map
            (fun p : Point (π ≫ y) τ.unop ↦ Point.closedPushforward π y p)
            (Rel_closedPushforward π y τ.unop)) =
      TypeCat.ofHom
          (_root_.Quotient.map
            (fun p : Point (π ≫ y) σ.unop ↦ Point.closedPushforward π y p)
            (Rel_closedPushforward π y σ.unop)) ≫
        (hilbert y).map h := sorry

/-- The natural transformation `Hilb_{X/B} ⟶ Hilb_{Y/B}` induced by a closed
immersion `π : X ⟶ Y` of algebraic spaces with `y : Y ⟶ B` separated. -/
@[expose] def closedMap (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    hilbert (π ≫ y) ⟶ hilbert y where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map
        (fun p : Point (π ≫ y) σ.unop ↦ Point.closedPushforward π y p)
        (Rel_closedPushforward π y σ.unop))
  naturality {_ _} h := closedMap_naturality π y h

/-- The component of `closedMap π y` at a scheme over `B` is the quotient map of
`Point.closedPushforward`, using that `y` is separated. -/
theorem closedMap_app (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (σ : (SchemeOver B)ᵒᵖ) :
    (closedMap π y).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun p : Point (π ≫ y) σ.unop ↦ Point.closedPushforward π y p)
          (Rel_closedPushforward π y σ.unop)) := sorry

/-- A closed immersion of algebraic spaces separated and of finite presentation
over `B` induces a closed immersion of Hilbert functors. -/
theorem isClosedImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    SchemeOver.IsClosedImmersion (closedMap π y) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
