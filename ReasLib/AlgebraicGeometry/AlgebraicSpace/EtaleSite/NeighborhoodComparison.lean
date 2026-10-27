/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion

public import Mathlib.CategoryTheory.Elements
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Neighborhood

/-!
# Comparison of small étale neighborhoods with étale neighborhoods of algebraic spaces

Scheme étale neighborhoods of a geometric point are the objects of `smallEtaleSite X` with a
chosen lift. The chart functor `smallEtaleToSpaces` sends their underlying schemes to represented
algebraic spaces, giving étale neighborhoods in `spacesEtaleSite X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The lift functor on the small étale site obtained by restricting `etaleLiftFunctor` along
`smallEtaleToSpaces`. -/
abbrev schemeLiftFunctor (xbar : GeometricPoint X) : smallEtaleSite X ⥤ Type (u + 1) :=
  smallEtaleToSpaces X ⋙ etaleLiftFunctor xbar

/-- `schemeLiftFunctor` is precomposition of `etaleLiftFunctor` with `smallEtaleToSpaces`. -/
theorem schemeLiftFunctor_eq (xbar : GeometricPoint X) :
    schemeLiftFunctor xbar = smallEtaleToSpaces X ⋙ etaleLiftFunctor xbar :=
  rfl

/-- Étale neighborhoods of a geometric point whose underlying object lies in `smallEtaleSite X`,
as the category of elements of `schemeLiftFunctor`. -/
abbrev SchemeEtaleNeighborhood (xbar : GeometricPoint X) :=
  (schemeLiftFunctor xbar).Elements

/-- The category of scheme étale neighborhoods is the category of elements of
`schemeLiftFunctor`. -/
theorem schemeEtaleNeighborhood_eq (xbar : GeometricPoint X) :
    SchemeEtaleNeighborhood xbar = (schemeLiftFunctor xbar).Elements :=
  rfl

/-- The inclusion of scheme étale neighborhoods into all étale neighborhoods. -/
abbrev SchemeEtaleNeighborhood.toEtaleNeighborhood (xbar : GeometricPoint X) :
    SchemeEtaleNeighborhood xbar ⥤ EtaleNeighborhood xbar :=
  Functor.Elements.precomp (smallEtaleToSpaces X) (etaleLiftFunctor xbar)

/-- On objects, `SchemeEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleToSpaces` and
keeps the same lift. -/
theorem SchemeEtaleNeighborhood.toEtaleNeighborhood_obj (xbar : GeometricPoint X)
    (U : SchemeEtaleNeighborhood xbar) :
    (SchemeEtaleNeighborhood.toEtaleNeighborhood xbar).obj U =
      Functor.elementsMk (etaleLiftFunctor xbar) ((smallEtaleToSpaces X).obj U.fst) U.snd :=
  rfl

/-- On morphisms, `SchemeEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleToSpaces` to
the underlying site morphism. -/
theorem SchemeEtaleNeighborhood.toEtaleNeighborhood_map (xbar : GeometricPoint X)
    {U V : SchemeEtaleNeighborhood xbar} (f : U ⟶ V) :
    ((SchemeEtaleNeighborhood.toEtaleNeighborhood xbar).map f).val =
      (smallEtaleToSpaces X).map f.val :=
  rfl

/-- The `Over X` morphism associated to the chosen lift of a small étale neighborhood. -/
def SmallEtaleNeighborhood.toSchemeLift {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((smallEtaleToSpaces X).obj N.toSite) :=
  Over.homMk N.lift N.lift_fac

/-- The left component of `toSchemeLift` is the algebraic-space lift of the neighborhood. -/
theorem SmallEtaleNeighborhood.toSchemeLift_left {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toSchemeLift N).left = N.lift :=
  rfl

/-- View a small étale neighborhood as a scheme étale neighborhood of `etaleLiftFunctor`. -/
def SmallEtaleNeighborhood.toSchemeEtaleNeighborhood {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) : SchemeEtaleNeighborhood xbar :=
  Functor.elementsMk (schemeLiftFunctor xbar) N.toSite (SmallEtaleNeighborhood.toSchemeLift N)

/-- The underlying small étale object of `toSchemeEtaleNeighborhood` is the original site
object. -/
theorem SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_toSite {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toSchemeEtaleNeighborhood N).fst = N.toSite :=
  rfl

/-- A morphism of small étale neighborhoods induces a morphism of scheme étale neighborhoods. -/
theorem SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_map_snd {xbar : GeometricPoint X}
    {N N' : SmallEtaleNeighborhood xbar} (f : N ⟶ N') :
    (schemeLiftFunctor xbar).map f.val (SmallEtaleNeighborhood.toSchemeLift N) =
      SmallEtaleNeighborhood.toSchemeLift N' := by
  apply Over.OverMorphism.ext
  change ofOverMap N.overHom ≫ ofOverMap f.val.left = ofOverMap N'.overHom
  calc
    ofOverMap N.overHom ≫ ofOverMap f.val.left =
        ofOverMap (N.overHom ≫ f.val.left) :=
      ((ofOverFunctor S).map_comp N.overHom f.val.left).symm
    _ = ofOverMap N'.overHom :=
      congrArg ofOverMap (congrArg CommaMorphism.left f.property)

/-- The functor from small étale neighborhoods to scheme étale neighborhoods of
`etaleLiftFunctor`. -/
def SmallEtaleNeighborhood.toSchemeEtaleNeighborhoodFunctor (xbar : GeometricPoint X) :
    SmallEtaleNeighborhood xbar ⥤ SchemeEtaleNeighborhood xbar where
  obj := SmallEtaleNeighborhood.toSchemeEtaleNeighborhood
  map f :=
    CategoryOfElements.homMk _ _ f.val
      (SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_map_snd f)
  map_id _ := by
    apply CategoryOfElements.ext
    rfl
  map_comp _ _ := by
    apply CategoryOfElements.ext
    rfl

/-- The functor from small étale neighborhoods to all étale neighborhoods of algebraic spaces. -/
def SmallEtaleNeighborhood.toEtaleNeighborhood (xbar : GeometricPoint X) :
    SmallEtaleNeighborhood xbar ⥤ EtaleNeighborhood xbar :=
  SmallEtaleNeighborhood.toSchemeEtaleNeighborhoodFunctor xbar ⋙
    SchemeEtaleNeighborhood.toEtaleNeighborhood xbar

/-- On objects, `SmallEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleToSpaces` to the
underlying site object and keeps the algebraic-space lift. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_obj (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N =
      EtaleNeighborhood.of ((smallEtaleToSpaces X).obj N.toSite) N.lift N.lift_fac :=
  rfl

/-- The underlying spaces-étale object of `SmallEtaleNeighborhood.toEtaleNeighborhood` is the
image under `smallEtaleToSpaces`. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_toSpacesEtale (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N).toSpacesEtale =
      (smallEtaleToSpaces X).obj N.toSite :=
  rfl

/-- The chosen lift is preserved by `SmallEtaleNeighborhood.toEtaleNeighborhood`. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_lift (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N).lift = N.lift :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
