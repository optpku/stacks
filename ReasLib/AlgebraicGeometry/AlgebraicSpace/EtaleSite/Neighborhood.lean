/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation

/-!
# Small étale neighborhoods of a geometric point

An étale neighborhood of a geometric point `xbar` of an algebraic space `X`, with domain an
object of the small étale site, is a lift of `xbar` through an étale morphism from a scheme
over the base into `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The functor sending an object `U` of the small étale site of `X` to the type of lifts of
a geometric point through the structure morphism of `U`. -/
def smallLiftFunctor (xbar : GeometricPoint X) : smallEtaleSite X ⥤ Type u :=
  MorphismProperty.CostructuredArrow.forget (@Etale S) ⊤ (ofOverFunctor S) X ⋙
    coyoneda.obj (op (CategoryTheory.CostructuredArrow.mk xbar.hom))

/-- The value of `smallLiftFunctor xbar` at `U` is the type of costructured-arrow morphisms from
`xbar` to `U`. -/
theorem smallLiftFunctor_obj (xbar : GeometricPoint X) (U : smallEtaleSite X) :
    (smallLiftFunctor xbar).obj U =
      (CategoryTheory.CostructuredArrow.mk xbar.hom ⟶
        (MorphismProperty.CostructuredArrow.forget (@Etale S) ⊤ (ofOverFunctor S) X).obj U) :=
  rfl

/-- The category of étale neighborhoods of a geometric point with domain an object of the
small étale site of `X`. -/
abbrev SmallEtaleNeighborhood (xbar : GeometricPoint X) :=
  (smallLiftFunctor xbar).Elements

/-- The category of étale neighborhoods is the category of elements of `smallLiftFunctor`. -/
theorem smallEtaleNeighborhood_eq (xbar : GeometricPoint X) :
    SmallEtaleNeighborhood xbar = (smallLiftFunctor xbar).Elements :=
  rfl

namespace SmallEtaleNeighborhood

variable {xbar : GeometricPoint X}

/-- The object of the small étale site underlying an étale neighborhood. -/
abbrev toSite (N : SmallEtaleNeighborhood xbar) : smallEtaleSite X :=
  N.1

/-- The morphism in `Over S` from the source of `xbar` to the domain of an étale neighborhood. -/
abbrev overHom (N : SmallEtaleNeighborhood xbar) :
    Over.mk xbar.structureHom ⟶ N.toSite.left :=
  N.2.left

/-- The algebraic-space lift of a geometric point to an étale neighborhood. -/
abbrev lift (N : SmallEtaleNeighborhood xbar) :
    ofOver (Over.mk xbar.structureHom) ⟶ ofOver N.toSite.left :=
  ofOverMap N.overHom

/-- The chosen lift of a geometric point commutes with the étale structure morphism. -/
theorem lift_fac (N : SmallEtaleNeighborhood xbar) :
    N.lift ≫ N.toSite.hom = xbar.hom :=
  CategoryTheory.CostructuredArrow.w N.2

/-- Construct an étale neighborhood from an object of the small étale site and a lift of the
geometric point. -/
def of (U : smallEtaleSite X) (u : Over.mk xbar.structureHom ⟶ U.left)
    (hu : ofOverMap u ≫ U.hom = xbar.hom) : SmallEtaleNeighborhood xbar :=
  Functor.elementsMk (smallLiftFunctor xbar) U
    (CategoryTheory.CostructuredArrow.homMk u hu)

/-- The underlying site object of `of U u hu` is `U`. -/
theorem of_toSite (U : smallEtaleSite X) (u : Over.mk xbar.structureHom ⟶ U.left)
    (hu : ofOverMap u ≫ U.hom = xbar.hom) :
    (of U u hu).toSite = U :=
  rfl

/-- The `Over S` morphism of `of U u hu` is the supplied lift. -/
theorem of_overHom (U : smallEtaleSite X) (u : Over.mk xbar.structureHom ⟶ U.left)
    (hu : ofOverMap u ≫ U.hom = xbar.hom) :
    (of U u hu).overHom = u :=
  rfl

/-- The algebraic-space lift of `of U u hu` is `ofOverMap` of the supplied morphism. -/
theorem of_lift (U : smallEtaleSite X) (u : Over.mk xbar.structureHom ⟶ U.left)
    (hu : ofOverMap u ≫ U.hom = xbar.hom) :
    (of U u hu).lift = ofOverMap u :=
  rfl

/-- A morphism of étale neighborhoods is a morphism in the category of elements. -/
abbrev Hom (V U : SmallEtaleNeighborhood xbar) :=
  V ⟶ U

namespace Hom

/-- The morphism of small étale site objects underlying a morphism of étale neighborhoods. -/
abbrev toSiteHom {V U : SmallEtaleNeighborhood xbar} (f : Hom V U) :
    V.toSite ⟶ U.toSite :=
  f.val

/-- The morphism in `Over S` underlying a morphism of étale neighborhoods. -/
abbrev overHom {V U : SmallEtaleNeighborhood xbar} (f : Hom V U) :
    V.toSite.left ⟶ U.toSite.left :=
  f.toSiteHom.left

/-- The scheme morphism underlying a morphism of étale neighborhoods. -/
abbrev schemeHom {V U : SmallEtaleNeighborhood xbar} (f : Hom V U) :
    V.toSite.left.left ⟶ U.toSite.left.left :=
  f.overHom.left

/-- A morphism of étale neighborhoods preserves the selected algebraic-space lifts. -/
theorem lift_fac {V U : SmallEtaleNeighborhood xbar} (f : Hom V U) :
    V.lift ≫ ofOverMap f.overHom = U.lift :=
  ((ofOverFunctor S).map_comp V.overHom f.overHom).symm.trans
    (congrArg (ofOverFunctor S).map
      (congrArg CategoryTheory.CostructuredArrow.Hom.left f.property))

/-- The `Over S` component of a neighborhood morphism identifies the selected lifts. -/
theorem overHom_fac {V U : SmallEtaleNeighborhood xbar} (f : Hom V U) :
    V.overHom ≫ f.overHom = U.overHom :=
  congrArg CategoryTheory.CostructuredArrow.Hom.left f.property

/-- Construct a morphism of étale neighborhoods from a morphism of small étale site objects
preserving the selected lifts. -/
def of {V U : SmallEtaleNeighborhood xbar} (f : V.toSite ⟶ U.toSite)
    (hf : V.overHom ≫ f.left = U.overHom) : Hom V U :=
  CategoryOfElements.homMk V U f (CategoryTheory.CostructuredArrow.hom_ext _ _ hf)

/-- The underlying scheme map of the neighborhood morphism constructed by `of` is the scheme
map of the supplied site morphism. -/
theorem of_schemeHom {V U : SmallEtaleNeighborhood xbar} (f : V.toSite ⟶ U.toSite)
    (hf : V.overHom ≫ f.left = U.overHom) :
    (of f hf).schemeHom = f.left.left :=
  rfl

end Hom

end SmallEtaleNeighborhood

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
