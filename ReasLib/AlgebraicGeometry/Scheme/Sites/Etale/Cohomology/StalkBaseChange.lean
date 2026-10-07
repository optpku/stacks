module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Neighborhood
public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

noncomputable section

/- Private implementation visibility justification: the public base-change morphisms use
private inverse-image squares and a private geometric-fiber comparison map. -/
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.Scheme.Etale.Cohomology

variable {X S : Scheme.{u}}

/-- Restriction to the closed geometric point gives a germ from strict-henselian derived
sections to the original geometric stalk. -/
def strictHenselianSectionsToStalk (s : GeometricPoint S) :
    Derived.inverseImage (StrictHenselization.toScheme S s) ⋙
        siteAbelianSectionsDerived.{u + 1, u, u + 1} (strictHenselizationAt S s).smallEtaleTopology
          (globalEtale (strictHenselizationAt S s)) ⟶
      (etaleStalkExact s).mapDerivedCategory :=
  whiskerLeft (Derived.inverseImage (StrictHenselization.toScheme S s))
      (Derived.sectionsPullback (StrictHenselization.closedPoint s)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight
      ((Derived.inverseImageCompIso (StrictHenselization.closedPoint s)
          (StrictHenselization.toScheme S s)).inv ≫
        (eqToIso (congrArg Derived.inverseImage
          (StrictHenselization.closedPoint_over s))).hom)
      (siteAbelianSectionsDerived.{u + 1, u, u + 1} (Spec (.of s.K)).smallEtaleTopology
        (globalEtale (Spec (.of s.K)))) ≫
    Derived.geometricPointSectionsToStalk s

/-- Derived sections on the pointed strict henselization identify with the geometric stalk. -/
theorem strictHenselianSectionsToStalk_isIso (s : GeometricPoint S) :
    IsIso (strictHenselianSectionsToStalk s) := sorry

/-- The geometric stalk identifies with derived sections on the pointed strict henselization. -/
def strictHenselianSectionsIso (s : GeometricPoint S) :
    (etaleStalkExact s).mapDerivedCategory ≅
      Derived.inverseImage (StrictHenselization.toScheme S s) ⋙
        siteAbelianSectionsDerived.{u + 1, u, u + 1} (strictHenselizationAt S s).smallEtaleTopology
          (globalEtale (strictHenselizationAt S s)) :=
  (@asIso _ _ _ _ (strictHenselianSectionsToStalk s)
    (strictHenselianSectionsToStalk_isIso s)).symm

/-- A commutative scheme square gives the canonical square of derived inverse images. -/
private def inverseImageSquare {X' S' : Scheme.{u}}
    (f : X ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    (commutes : p ≫ f = f' ≫ g) :
    Derived.inverseImage g ⋙ Derived.inverseImage f' ≅
      Derived.inverseImage f ⋙ Derived.inverseImage p :=
  (Derived.inverseImageCompIso f' g).symm ≪≫
    eqToIso (congrArg Derived.inverseImage commutes.symm) ≪≫
    Derived.inverseImageCompIso p f

/-- The closed point induces the canonical map from the geometric fiber to the
strict-henselian base change. -/
private def geometricFiberToStrictHenselization (f : X ⟶ S) (s : GeometricPoint S) :
    pullback f s.hom ⟶ pullback f (StrictHenselization.toScheme S s) :=
  pullback.map f s.hom f (StrictHenselization.toScheme S s)
    (𝟙 X) (StrictHenselization.closedPoint s) (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id s.hom).trans (StrictHenselization.closedPoint_over s).symm)

/-- The canonical map from the stalk of a derived direct image to derived sections of its
inverse image on the strict-henselian base change. -/
def etaleStalkToStrictHenselizationCohomology (f : X ⟶ S) (s : GeometricPoint S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (etaleStalkExact s).mapDerivedCategory.obj ((Derived.directImage f).obj K) ⟶
      (siteAbelianSectionsDerived.{u + 1, u, u + 1}
        (pullback f (StrictHenselization.toScheme S s)).smallEtaleTopology
        (globalEtale (pullback f (StrictHenselization.toScheme S s)))).obj
          ((Derived.inverseImage
            (pullback.fst f (StrictHenselization.toScheme S s))).obj K) :=
  let structural := StrictHenselization.toScheme S s
  let projection := pullback.fst f structural
  let baseChange := pullback.snd f structural
  (strictHenselianSectionsIso s).hom.app ((Derived.directImage f).obj K) ≫
    (siteAbelianSectionsDerived.{u + 1, u, u + 1} (strictHenselizationAt S s).smallEtaleTopology
      (globalEtale (strictHenselizationAt S s))).map
      (DerivedBaseChange.app (Derived.adjunction f) (Derived.adjunction baseChange)
        (inverseImageSquare f projection baseChange structural (pullback.condition ..)) K) ≫
    (Derived.directImageSectionsIso baseChange).hom.app
      ((Derived.inverseImage projection).obj K)

/-- The canonical map from strict-henselian base-change cohomology to geometric-fiber
cohomology, with inverse images transported to the geometric-fiber projection. -/
def strictHenselizationToGeometricFiberCohomology (f : X ⟶ S) (s : GeometricPoint S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (siteAbelianSectionsDerived.{u + 1, u, u + 1}
      (pullback f (StrictHenselization.toScheme S s)).smallEtaleTopology
      (globalEtale (pullback f (StrictHenselization.toScheme S s)))).obj
        ((Derived.inverseImage
          (pullback.fst f (StrictHenselization.toScheme S s))).obj K) ⟶
      (siteAbelianSectionsDerived.{u + 1, u, u + 1} (pullback f s.hom).smallEtaleTopology
        (globalEtale (pullback f s.hom))).obj
          ((Derived.inverseImage (pullback.fst f s.hom)).obj K) :=
  let structural := StrictHenselization.toScheme S s
  let projection := pullback.fst f structural
  let baseChange := pullback.snd f structural
  let closedPoint := StrictHenselization.closedPoint s
  let fiberProjection := pullback.fst f s.hom
  let fiberMorphism := pullback.snd f s.hom
  let comparison := geometricFiberToStrictHenselization f s
  let firstCommutes : comparison ≫ projection = fiberProjection ≫ 𝟙 X :=
    pullback.lift_fst _ _ _
  let secondCommutes : comparison ≫ baseChange = fiberMorphism ≫ closedPoint :=
    pullback.lift_snd _ _ _
  let projectionTransport := (Derived.inverseImageCompIso comparison projection).inv.app K ≫
    (eqToIso (congrArg (fun morphism => (Derived.inverseImage morphism).obj K)
      (firstCommutes.trans (Category.comp_id fiberProjection)))).hom
  (Derived.directImageSectionsIso baseChange).inv.app
      ((Derived.inverseImage projection).obj K) ≫
    (Derived.sectionsPullback closedPoint).app
      ((Derived.directImage baseChange).obj ((Derived.inverseImage projection).obj K)) ≫
    (siteAbelianSectionsDerived.{u + 1, u, u + 1} (Spec (.of s.K)).smallEtaleTopology
      (globalEtale (Spec (.of s.K)))).map
      (DerivedBaseChange.app (Derived.adjunction baseChange) (Derived.adjunction fiberMorphism)
        (inverseImageSquare baseChange comparison fiberMorphism closedPoint secondCommutes)
        ((Derived.inverseImage projection).obj K)) ≫
    (Derived.directImageSectionsIso fiberMorphism).hom.app
      ((Derived.inverseImage comparison).obj ((Derived.inverseImage projection).obj K)) ≫
    (siteAbelianSectionsDerived.{u + 1, u, u + 1} (pullback f s.hom).smallEtaleTopology
      (globalEtale (pullback f s.hom))).map projectionTransport

/-- The usual geometric-fiber base-change map, formed directly from the square over the
geometric point, without an intermediate strict henselization. -/
def etaleStalkToGeometricFiberBaseChange (f : X ⟶ S) (s : GeometricPoint S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (etaleStalkExact s).mapDerivedCategory.obj ((Derived.directImage f).obj K) ⟶
      (siteAbelianSectionsDerived.{u + 1, u, u + 1} (pullback f s.hom).smallEtaleTopology
        (globalEtale (pullback f s.hom))).obj
          ((Derived.inverseImage (pullback.fst f s.hom)).obj K) :=
  let projection := pullback.fst f s.hom
  let fiberMorphism := pullback.snd f s.hom
  (Derived.geometricPointSectionsIso s).hom.app ((Derived.directImage f).obj K) ≫
    (siteAbelianSectionsDerived.{u + 1, u, u + 1} (Spec (.of s.K)).smallEtaleTopology
      (globalEtale (Spec (.of s.K)))).map
      (DerivedBaseChange.app (Derived.adjunction f) (Derived.adjunction fiberMorphism)
        (inverseImageSquare f projection fiberMorphism s.hom (pullback.condition ..)) K) ≫
    (Derived.directImageSectionsIso fiberMorphism).hom.app
      ((Derived.inverseImage projection).obj K)

/-- The stalk-to-strict-henselian cohomology map followed by the geometric-fiber comparison
equals the usual geometric-fiber base-change map. -/
theorem etaleStalkBaseChange_factorization (f : X ⟶ S) (s : GeometricPoint S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleStalkToStrictHenselizationCohomology f s K ≫
        strictHenselizationToGeometricFiberCohomology f s K =
      etaleStalkToGeometricFiberBaseChange f s K := sorry

end AlgebraicGeometry.Scheme.Etale.Cohomology

end
