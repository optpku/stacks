/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Locality of finite presentation for morphisms of algebraic spaces

This file records pointwise, base-change, covering, and étale-square
characterizations of the locally finite presentation property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is locally of finite presentation at a point when its restriction
to an open neighbourhood of that point has the property. -/
def FinitePresentationAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      LocallyOfFinitePresentation (i ≫ f)

/-- The pointwise property unfolds to an open neighbourhood with locally finite
presentation restriction. -/
theorem finitePresentationAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    FinitePresentationAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFinitePresentation (i ≫ f) :=
  Iff.rfl

namespace LocallyOfFinitePresentation

/-- Every base change along a morphism from a scheme is locally of finite
presentation. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    LocallyOfFinitePresentation (pullbackAlongScheme.snd f g)

/-- Every base change along a morphism from an affine scheme is locally of finite
presentation. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → LocallyOfFinitePresentation (pullbackAlongScheme.snd f g)

/-- A surjective étale scheme cover of the target makes the base change locally
of finite presentation. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ LocallyOfFinitePresentation (pullbackAlongScheme.snd f b)

/-- A surjective étale scheme cover of the source has locally finite presentation
composite with the given morphism. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ LocallyOfFinitePresentation (φ ≫ f)

/-- Every commutative étale scheme square over the morphism has locally finite
presentation top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b →
          AlgebraicGeometry.LocallyOfFinitePresentation h.left

/-- There is a commutative étale scheme square over the morphism whose source
vertical map is surjective and whose top arrow is locally of finite
presentation. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.LocallyOfFinitePresentation h.left

/-- There are Zariski coverings of the target and its full inverse images on
which the restricted morphisms are locally of finite presentation. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, LocallyOfFinitePresentation (h j)) ∧
          Set.range (Points.map ι) =
            (Points.map f) ⁻¹' Set.range (Points.map (𝒱.f i))

end LocallyOfFinitePresentation

/-- The nine standard locality conditions for local finite presentation are
equivalent. -/
theorem locallyOfFinitePresentation_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFinitePresentation f
      , ∀ x : Points X, FinitePresentationAt f x
      , LocallyOfFinitePresentation.baseChangeOnSchemes f
      , LocallyOfFinitePresentation.baseChangeOnAffineSchemes f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleTarget f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleSource f
      , LocallyOfFinitePresentation.forallEtaleSquare f
      , LocallyOfFinitePresentation.existsEtaleSquare f
      , LocallyOfFinitePresentation.existsZariskiCover.{u, v} f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
