/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import Mathlib.Data.List.TFAE

/-!
# Smooth morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is smooth if every
commutative square with étale vertical arrows from schemes has smooth top
arrow. -/
class Smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has smooth top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Smooth h.left

/-- A morphism of algebraic spaces is smooth if and only if every commutative
square with étale vertical arrows from schemes has smooth top arrow. -/
theorem smooth_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Smooth f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Smooth h.left :=
  sorry

namespace Smooth

/-- An étale scheme square over a smooth morphism of algebraic spaces has smooth
top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Smooth h.left :=
  sorry

/-- The identity morphism of an algebraic space is smooth. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Smooth (𝟙 X) :=
  sorry

end Smooth

/-- A morphism `f : X ⟶ Y` of algebraic spaces is smooth at a point `x` of `X`
if it is smooth after restriction to some open subspace neighbourhood of `x`. -/
def SmoothAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Smooth (i ≫ f)

/-- Smoothness at a point is the existence of an open subspace neighbourhood on
which the morphism is smooth. -/
theorem smoothAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    SmoothAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Smooth (i ≫ f) :=
  Iff.rfl

namespace Smooth

/-- Every base change of `f` along a morphism from a scheme is smooth. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Smooth (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is smooth. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Smooth (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is smooth. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Smooth (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is smooth. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧ Surjective φ ∧ Smooth (φ ≫ f)

/-- Every étale scheme square over `f` has smooth top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Smooth h.left

/-- There is an étale scheme square over `f` with surjective source cover and
smooth top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Smooth h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are smooth. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Smooth (h j)) ∧
          Set.range (Points.map ι) = (Points.map f) ⁻¹' Set.range (Points.map (𝒱.f i))

end Smooth


/-- Smoothness of a morphism of algebraic spaces is equivalent to pointwise
smoothness, smoothness after scheme or affine-scheme base change, smoothness on
surjective étale target or source covers, the universal or existential étale
scheme-square criterion, and smoothness on Zariski covers of the target and its
inverse images. -/
theorem smooth_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Smooth f
      , ∀ x : Points X, SmoothAt f x
      , Smooth.baseChangeOnSchemes f
      , Smooth.baseChangeOnAffineSchemes f
      , Smooth.existsSurjectiveEtaleTarget f
      , Smooth.existsSurjectiveEtaleSource f
      , Smooth.forallEtaleSquare f
      , Smooth.existsEtaleSquare f
      , Smooth.existsZariskiCover.{u, v} f ] :=
  sorry

/-- A smooth morphism of algebraic spaces is locally of finite type. -/
instance locallyOfFiniteType_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] : LocallyOfFiniteType f :=
  sorry

/-- A smooth morphism of algebraic spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_smooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
