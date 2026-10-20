/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Flat algebraic spaces over Artinian local algebras

Objects consist of an Artinian local algebra and an algebraic space flat over
its spectrum. Morphisms have covariant base arrows and contravariant space
arrows forming cartesian squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Functor

noncomputable section

universe u

namespace FlatAlgebraicSpaceCat

/-- The spectrum of the base ring. -/
abbrev specBase (Λ : Type u) [CommRing Λ] : Scheme.{u} :=
  Spec (CommRingCat.of Λ)

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The spectrum structure morphism induced by the stored algebra structure. -/
def specHom (A : ArtinianLocalAlgCat Λ k) :
    Spec (CommRingCat.of A.carrier) ⟶ specBase Λ :=
  Spec.map (CommRingCat.ofHom (@algebraMap Λ A.carrier _ _ A.algebra))

/-- The algebraic space represented by the spectrum of an Artinian local algebra. -/
def specObj (A : ArtinianLocalAlgCat Λ k) : AlgebraicSpace (specBase Λ) :=
  ofOver (Over.mk (specHom A))

/-- The spectrum algebraic space is represented by its spectrum structure morphism. -/
theorem specObj_eq (A : ArtinianLocalAlgCat Λ k) :
    specObj A = ofOver (Over.mk (specHom A)) := sorry

/-- Spectrum maps of algebra morphisms commute with their structure morphisms. -/
theorem specMap_w {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specHom A = specHom B := sorry

/-- The contravariant spectrum map of an Artinian local algebra morphism. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specObj B ⟶ specObj A :=
  yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (specMap_w f))

/-- The spectrum map is the Yoneda image of its morphism of schemes over the base. -/
theorem specMap_eq {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specMap f = yoneda.map
      (Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (specMap_w f) :
        Over.mk (specHom B) ⟶ Over.mk (specHom A)) := sorry

end FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

open FlatAlgebraicSpaceCat (specBase specObj specMap)

/-- An Artinian local algebra together with an algebraic space flat over its spectrum. -/
def FlatAlgebraicSpaceCat : Type (u + 1) :=
  Σ A : ArtinianLocalAlgCat Λ k, Σ X : AlgebraicSpace (specBase Λ),
    { structureHom : X ⟶ specObj A // AlgebraicSpace.Flat structureHom }

namespace FlatAlgebraicSpaceCat

variable {Λ k}

/-- The base algebra of a flat algebraic space over an Artinian local algebra. -/
def base (X : FlatAlgebraicSpaceCat Λ k) : ArtinianLocalAlgCat Λ k := X.1

/-- The underlying algebraic space over the spectrum of the base ring. -/
def space (X : FlatAlgebraicSpaceCat Λ k) : AlgebraicSpace (specBase Λ) := X.2.1

/-- The structure morphism to the spectrum of the stored Artinian local algebra. -/
def structureHom (X : FlatAlgebraicSpaceCat Λ k) : X.space ⟶ specObj X.base := X.2.2.1

/-- The stored structure morphism of a flat algebraic space is flat. -/
abbrev isFlat (X : FlatAlgebraicSpaceCat Λ k) : AlgebraicSpace.Flat X.structureHom := X.2.2.2

/-- Pair an Artinian local algebra with an algebraic space flat over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (X : AlgebraicSpace (specBase Λ))
    (structureHom : X ⟶ specObj A) (hflat : AlgebraicSpace.Flat structureHom) :
    FlatAlgebraicSpaceCat Λ k :=
  ⟨A, X, structureHom, hflat⟩

/-- The constructor recovers its base, space, structure morphism, and flatness. -/
theorem of_spec (A : ArtinianLocalAlgCat Λ k) (X : AlgebraicSpace (specBase Λ))
    (structureHom : X ⟶ specObj A) (hflat : AlgebraicSpace.Flat structureHom) :
    (of A X structureHom hflat).base = A ∧
      (of A X structureHom hflat).space = X ∧
      (of A X structureHom hflat).structureHom = structureHom ∧
      AlgebraicSpace.Flat (of A X structureHom hflat).structureHom := sorry

/-- A covariant base arrow and a contravariant space arrow forming a cartesian square. -/
def Hom (Y X : FlatAlgebraicSpaceCat Λ k) : Type (u + 1) :=
  Σ baseHom : Y.base ⟶ X.base,
    { spaceHom : X.space ⟶ Y.space //
      IsPullback spaceHom X.structureHom Y.structureHom (specMap baseHom) }

namespace Hom

/-- The base arrow of a cartesian morphism of flat algebraic spaces. -/
def baseHom {Y X : FlatAlgebraicSpaceCat Λ k} (f : Hom Y X) : Y.base ⟶ X.base := f.1

/-- The oppositely directed space arrow of a cartesian morphism. -/
def spaceHom {Y X : FlatAlgebraicSpaceCat Λ k} (f : Hom Y X) : X.space ⟶ Y.space := f.2.1

/-- The square underlying a morphism of flat algebraic spaces is cartesian. -/
abbrev isPullback {Y X : FlatAlgebraicSpaceCat Λ k} (f : Hom Y X) :
    IsPullback f.spaceHom X.structureHom Y.structureHom (specMap f.baseHom) := f.2.2

/-- Construct a cartesian morphism from its base arrow, space arrow, and pullback condition. -/
def of {Y X : FlatAlgebraicSpaceCat Λ k} (baseHom : Y.base ⟶ X.base)
    (spaceHom : X.space ⟶ Y.space)
    (isPullback : IsPullback spaceHom X.structureHom Y.structureHom (specMap baseHom)) :
    Hom Y X :=
  ⟨baseHom, spaceHom, isPullback⟩

/-- The identity cartesian morphism has identity base and space arrows. -/
def id (X : FlatAlgebraicSpaceCat Λ k) : Hom X X :=
  of (𝟙 X.base) (𝟙 X.space) sorry

/-- Composition composes base arrows covariantly and space arrows in reverse order. -/
def comp {X Y Z : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  of (f.baseHom ≫ g.baseHom) (g.spaceHom ≫ f.spaceHom) sorry

/-- A cartesian morphism has a pullback square and satisfies its commutativity equation. -/
theorem spec {Y X : FlatAlgebraicSpaceCat Λ k} (f : Hom Y X) :
    IsPullback f.spaceHom X.structureHom Y.structureHom (specMap f.baseHom) ∧
      f.spaceHom ≫ Y.structureHom = X.structureHom ≫ specMap f.baseHom := sorry

/-- The identity cartesian morphism has identity base arrow. -/
theorem id_baseHom (X : FlatAlgebraicSpaceCat Λ k) : (id X).baseHom = 𝟙 X.base := sorry

/-- The base arrow of a composite is the composite of the base arrows. -/
theorem comp_baseHom {X Y Z : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

end Hom

/-- Flat algebraic spaces over Artinian local algebras form a category with cartesian morphisms. -/
instance category : Category.{u + 1} (FlatAlgebraicSpaceCat Λ k) :=
  let laws :
      (∀ {X Y : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y), Hom.comp (Hom.id X) f = f) ∧
      (∀ {X Y : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y), Hom.comp f (Hom.id Y) = f) ∧
      (∀ {W X Y Z : FlatAlgebraicSpaceCat Λ k} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
        Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) := sorry
  { Hom := Hom, id := Hom.id, comp := Hom.comp,
    id_comp := laws.1, comp_id := laws.2.1, assoc := laws.2.2 }

variable (Λ k)

/-- The projection sends a flat algebraic space to its base and a cartesian morphism to its base arrow. -/
def forget : FlatAlgebraicSpaceCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id := Hom.id_baseHom
  map_comp := Hom.comp_baseHom

/-- The projection functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FlatAlgebraicSpaceCat Λ k) : (forget Λ k).obj X = X.base := sorry

/-- The projection functor sends a cartesian morphism to its base arrow. -/
theorem forget_map {Y X : FlatAlgebraicSpaceCat Λ k} (f : Y ⟶ X) :
    (forget Λ k).map f = f.baseHom := sorry

/-- The projection from flat algebraic spaces to Artinian local algebras is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Λ k).op := sorry

end FlatAlgebraicSpaceCat
