module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap66.Definition_66_19_2_EtaleNeighborhood
public import stacks_project.Chap66.Definition_66_19_6_Neighborhood

/-!
# Comparison of small étale neighborhoods with étale neighborhoods of algebraic spaces

Scheme étale neighborhoods of a geometric point are the objects of `smallEtaleSite X` with a
chosen lift. They include into the étale neighborhoods in `spacesEtaleSite X` by the identity-
on-objects functor `smallEtaleInclusion`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The lift functor on the small étale site obtained by restricting `etaleLiftFunctor` along
`smallEtaleInclusion`. -/
abbrev schemeLiftFunctor (xbar : GeometricPoint X) : smallEtaleSite X ⥤ Type (u + 1) :=
  smallEtaleInclusion X ⋙ etaleLiftFunctor xbar

/-- `schemeLiftFunctor` is precomposition of `etaleLiftFunctor` with `smallEtaleInclusion`. -/
theorem schemeLiftFunctor_eq (xbar : GeometricPoint X) :
    schemeLiftFunctor xbar = smallEtaleInclusion X ⋙ etaleLiftFunctor xbar :=
  sorry

/-- Étale neighborhoods of a geometric point whose underlying object lies in `smallEtaleSite X`,
as the category of elements of `schemeLiftFunctor`. -/
abbrev SchemeEtaleNeighborhood (xbar : GeometricPoint X) :=
  (schemeLiftFunctor xbar).Elements

/-- The category of scheme étale neighborhoods is the category of elements of
`schemeLiftFunctor`. -/
theorem schemeEtaleNeighborhood_eq (xbar : GeometricPoint X) :
    SchemeEtaleNeighborhood xbar = (schemeLiftFunctor xbar).Elements :=
  sorry

/-- The inclusion of scheme étale neighborhoods into all étale neighborhoods. -/
abbrev SchemeEtaleNeighborhood.toEtaleNeighborhood (xbar : GeometricPoint X) :
    SchemeEtaleNeighborhood xbar ⥤ EtaleNeighborhood xbar :=
  Functor.Elements.precomp (smallEtaleInclusion X) (etaleLiftFunctor xbar)

/-- On objects, `SchemeEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleInclusion` and
keeps the same lift. -/
theorem SchemeEtaleNeighborhood.toEtaleNeighborhood_obj (xbar : GeometricPoint X)
    (U : SchemeEtaleNeighborhood xbar) :
    (SchemeEtaleNeighborhood.toEtaleNeighborhood xbar).obj U =
      Functor.elementsMk (etaleLiftFunctor xbar) ((smallEtaleInclusion X).obj U.fst) U.snd :=
  sorry

/-- On morphisms, `SchemeEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleInclusion` to
the underlying site morphism. -/
theorem SchemeEtaleNeighborhood.toEtaleNeighborhood_map (xbar : GeometricPoint X)
    {U V : SchemeEtaleNeighborhood xbar} (f : U ⟶ V) :
    ((SchemeEtaleNeighborhood.toEtaleNeighborhood xbar).map f).val =
      (smallEtaleInclusion X).map f.val :=
  sorry

/-- The `Over X` morphism associated to the chosen lift of a small étale neighborhood. -/
def SmallEtaleNeighborhood.toSchemeLift {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    Over.mk xbar.hom ⟶
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj ((smallEtaleInclusion X).obj N.toSite) :=
  Over.homMk N.lift N.lift_fac

/-- The left component of `toSchemeLift` is the algebraic-space lift of the neighborhood. -/
theorem SmallEtaleNeighborhood.toSchemeLift_left {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toSchemeLift N).left = N.lift :=
  sorry

/-- View a small étale neighborhood as a scheme étale neighborhood of `etaleLiftFunctor`. -/
def SmallEtaleNeighborhood.toSchemeEtaleNeighborhood {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) : SchemeEtaleNeighborhood xbar :=
  Functor.elementsMk (schemeLiftFunctor xbar) N.toSite (SmallEtaleNeighborhood.toSchemeLift N)

/-- The underlying small étale object of `toSchemeEtaleNeighborhood` is the original site
object. -/
theorem SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_toSite {xbar : GeometricPoint X}
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toSchemeEtaleNeighborhood N).fst = N.toSite :=
  sorry

/-- A morphism of small étale neighborhoods induces a morphism of scheme étale neighborhoods. -/
theorem SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_map_snd {xbar : GeometricPoint X}
    {N N' : SmallEtaleNeighborhood xbar} (f : N ⟶ N') :
    (schemeLiftFunctor xbar).map f.val (SmallEtaleNeighborhood.toSchemeLift N) =
      SmallEtaleNeighborhood.toSchemeLift N' :=
  sorry

/-- The functor from small étale neighborhoods to scheme étale neighborhoods of
`etaleLiftFunctor`. -/
def SmallEtaleNeighborhood.toSchemeEtaleNeighborhoodFunctor (xbar : GeometricPoint X) :
    SmallEtaleNeighborhood xbar ⥤ SchemeEtaleNeighborhood xbar where
  obj := SmallEtaleNeighborhood.toSchemeEtaleNeighborhood
  map f :=
    CategoryOfElements.homMk _ _ f.val
      (SmallEtaleNeighborhood.toSchemeEtaleNeighborhood_map_snd f)
  map_id := sorry
  map_comp := sorry

/-- The functor from small étale neighborhoods to all étale neighborhoods of algebraic spaces. -/
def SmallEtaleNeighborhood.toEtaleNeighborhood (xbar : GeometricPoint X) :
    SmallEtaleNeighborhood xbar ⥤ EtaleNeighborhood xbar :=
  SmallEtaleNeighborhood.toSchemeEtaleNeighborhoodFunctor xbar ⋙
    SchemeEtaleNeighborhood.toEtaleNeighborhood xbar

/-- On objects, `SmallEtaleNeighborhood.toEtaleNeighborhood` applies `smallEtaleInclusion` to the
underlying site object and keeps the algebraic-space lift. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_obj (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    (SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N =
      EtaleNeighborhood.of ((smallEtaleInclusion X).obj N.toSite) N.lift N.lift_fac :=
  sorry

/-- The underlying spaces-étale object of `SmallEtaleNeighborhood.toEtaleNeighborhood` is the
image under `smallEtaleInclusion`. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_toSpacesEtale (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N).toSpacesEtale =
      (smallEtaleInclusion X).obj N.toSite :=
  sorry

/-- The chosen lift is preserved by `SmallEtaleNeighborhood.toEtaleNeighborhood`. -/
theorem SmallEtaleNeighborhood.toEtaleNeighborhood_lift (xbar : GeometricPoint X)
    (N : SmallEtaleNeighborhood xbar) :
    ((SmallEtaleNeighborhood.toEtaleNeighborhood xbar).obj N).lift = N.lift :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
