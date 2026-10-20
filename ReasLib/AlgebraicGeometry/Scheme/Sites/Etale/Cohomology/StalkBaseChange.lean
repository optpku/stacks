/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

/-- Abelian-group presheaves on the small étale site have canonical left-exact sheafification. -/
private abbrev sectionsSheafification (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (@instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
          T.Etale inferInstance T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
          (fun P U cover ↦ inferInstance) (fun U ↦ inferInstance)
          _ _ inferInstance inferInstance
          (fun U ↦ @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
            (CategoryTheory.forget AddCommGrpCat.{u + 1})
            AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
            (T.smallEtaleTopology.Cover U)ᵒᵖ inferInstance
            (@isFiltered_op_of_isCofiltered (T.smallEtaleTopology.Cover U) inferInstance
              (isCofiltered_of_semilatticeInf_nonempty (T.smallEtaleTopology.Cover U)))) inferInstance
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))

/-- Abelian étale sheaves form an abelian category via left-exact sheafification. -/
private abbrev sectionsAbelian (T : Scheme.{u}) :
    CategoryTheory.Abelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  @sheafIsAbelian _ _ _ _ inferInstance _ (sectionsSheafification T)

/-- Derived global étale sections with canonical sheafification. -/
private abbrev globalSectionsDerived (T : Scheme.{u}) :=
  @siteAbelianSectionsDerived.{u + 1, u, u + 1} T.Etale inferInstance
    T.smallEtaleTopology (globalEtale T) (sectionsSheafification T) inferInstance

/-- Restriction to the closed geometric point gives a germ from strict-henselian derived
sections to the original geometric stalk. -/
def strictHenselianSectionsToStalk (s : GeometricPoint S) :
    Derived.inverseImage (StrictHenselization.toScheme S s) ⋙
        globalSectionsDerived (strictHenselizationAt S s) ⟶
      (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _
      (etaleStalkExact s)) :=
  whiskerLeft (Derived.inverseImage (StrictHenselization.toScheme S s))
      (Derived.sectionsPullback (StrictHenselization.closedPoint s)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight
      ((Derived.inverseImageCompIso (StrictHenselization.closedPoint s)
          (StrictHenselization.toScheme S s)).inv ≫
        (eqToIso (congrArg (fun morphism : Spec (.of s.K) ⟶ S => Derived.inverseImage morphism)
          (StrictHenselization.closedPoint_over s))).hom)
      (globalSectionsDerived (Spec (.of s.K))) ≫
    Derived.geometricPointSectionsToStalk s

/-- Derived sections on the pointed strict henselization identify with the geometric stalk. -/
theorem strictHenselianSectionsToStalk_isIso (s : GeometricPoint S) :
    IsIso (strictHenselianSectionsToStalk s) := sorry

/-- The geometric stalk identifies with derived sections on the pointed strict henselization. -/
def strictHenselianSectionsIso (s : GeometricPoint S) :
    (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _
      (etaleStalkExact s)) ≅
      Derived.inverseImage (StrictHenselization.toScheme S s) ⋙
        globalSectionsDerived (strictHenselizationAt S s) :=
  (@asIso _ _ _ _ (strictHenselianSectionsToStalk s)
    (strictHenselianSectionsToStalk_isIso s)).symm

/-- A commutative scheme square gives the canonical square of derived inverse images. -/
private def inverseImageSquare {X' S' : Scheme.{u}}
    (f : X ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    (commutes : p ≫ f = f' ≫ g) :
    Derived.inverseImage g ⋙ Derived.inverseImage f' ≅
      Derived.inverseImage f ⋙ Derived.inverseImage p :=
  (Derived.inverseImageCompIso f' g).symm ≪≫
    eqToIso (congrArg (fun morphism : X' ⟶ S => Derived.inverseImage morphism) commutes.symm) ≪≫
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
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _
      (etaleStalkExact s)).obj ((Derived.directImage f).obj K) ⟶
      (globalSectionsDerived (pullback f (StrictHenselization.toScheme S s))).obj
          ((Derived.inverseImage
            (pullback.fst f (StrictHenselization.toScheme S s))).obj K) :=
  let structural := StrictHenselization.toScheme S s
  let projection := pullback.fst f structural
  let baseChange := pullback.snd f structural
  (strictHenselianSectionsIso s).hom.app ((Derived.directImage f).obj K) ≫
    (globalSectionsDerived (strictHenselizationAt S s)).map
      (DerivedBaseChange.app (Derived.adjunction f) (Derived.adjunction baseChange)
        (inverseImageSquare f projection baseChange structural (pullback.condition ..)) K) ≫
    (Derived.directImageSectionsIso baseChange).hom.app
      ((Derived.inverseImage projection).obj K)

/-- The canonical map from strict-henselian base-change cohomology to geometric-fiber
cohomology, with inverse images transported to the geometric-fiber projection. -/
def strictHenselizationToGeometricFiberCohomology (f : X ⟶ S) (s : GeometricPoint S)
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    (globalSectionsDerived (pullback f (StrictHenselization.toScheme S s))).obj
        ((Derived.inverseImage
          (pullback.fst f (StrictHenselization.toScheme S s))).obj K) ⟶
      (globalSectionsDerived (pullback f s.hom)).obj
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
    (globalSectionsDerived (Spec (.of s.K))).map
      (DerivedBaseChange.app (Derived.adjunction baseChange) (Derived.adjunction fiberMorphism)
        (inverseImageSquare baseChange comparison fiberMorphism closedPoint secondCommutes)
        ((Derived.inverseImage projection).obj K)) ≫
    (Derived.directImageSectionsIso fiberMorphism).hom.app
      ((Derived.inverseImage comparison).obj ((Derived.inverseImage projection).obj K)) ≫
    (globalSectionsDerived (pullback f s.hom)).map projectionTransport

/-- The usual geometric-fiber base-change map, formed directly from the square over the
geometric point, without an intermediate strict henselization. -/
def etaleStalkToGeometricFiberBaseChange (f : X ⟶ S) (s : GeometricPoint S)
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    (@ExactFunctor.mapDerivedCategory _ _ (sectionsAbelian S) _ _ _ _ _
      (etaleStalkExact s)).obj ((Derived.directImage f).obj K) ⟶
      (globalSectionsDerived (pullback f s.hom)).obj
          ((Derived.inverseImage (pullback.fst f s.hom)).obj K) :=
  let projection := pullback.fst f s.hom
  let fiberMorphism := pullback.snd f s.hom
  (Derived.geometricPointSectionsIso s).hom.app ((Derived.directImage f).obj K) ≫
    (globalSectionsDerived (Spec (.of s.K))).map
      (DerivedBaseChange.app (Derived.adjunction f) (Derived.adjunction fiberMorphism)
        (inverseImageSquare f projection fiberMorphism s.hom (pullback.condition ..)) K) ≫
    (Derived.directImageSectionsIso fiberMorphism).hom.app
      ((Derived.inverseImage projection).obj K)

/-- The stalk-to-strict-henselian cohomology map followed by the geometric-fiber comparison
equals the usual geometric-fiber base-change map. -/
theorem etaleStalkBaseChange_factorization (f : X ⟶ S) (s : GeometricPoint S)
    (K : @DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      inferInstance (sectionsAbelian X) inferInstance) :
    etaleStalkToStrictHenselizationCohomology f s K ≫
        strictHenselizationToGeometricFiberCohomology f s K =
      etaleStalkToGeometricFiberBaseChange f s K := sorry

end AlgebraicGeometry.Scheme.Etale.Cohomology

end
