/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Abelian
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

-- Construct sheafification using the inf-semilattice of covering sieves.
attribute [local instance 2000] isCofiltered_of_semilatticeInf_nonempty

/-- Abelian coefficients in a universe containing the small étale site. -/
abbrev Coefficients (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- The actual unbounded derived category of abelian étale sheaves. -/
abbrev Complexes (X : Scheme.{u}) := DerivedCategory (Coefficients X)

/-- Abelian étale sheaves have the canonical Grothendieck structure in the site universe. -/
instance coefficientsGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Coefficients X) := inferInstance

/-- The identity object of the small étale site. -/
abbrev unitObject (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk _ (𝟙 X) inferInstance

/-- The canonical inverse image, left adjoint to étale direct image. -/
abbrev inverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Coefficients Y ⥤ Coefficients X :=
  Etale.Abelian.inverseImage f

/-- The canonical action of exact étale inverse image on derived categories. -/
abbrev derivedInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Complexes Y ⥤ Complexes X :=
  (inverseImage f).mapDerivedCategory

/-- Global sections, evaluated at the identity étale object. -/
abbrev sections (X : Scheme.{u}) : Coefficients X ⥤ AddCommGrpCat.{u + 1} :=
  siteAbelianSectionsFunctor X.smallEtaleTopology (unitObject X)

/-- Unbounded derived global sections with its right-derived universal property. -/
abbrev derivedSections (X : Scheme.{u}) :
    Complexes X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  Cochain.functor (sections X)

/-- The canonical map from the identity étale object to its base-changed presentation. -/
def unitToPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    unitObject X ⟶ (smallEtalePullback f).obj (unitObject Y) :=
  MorphismProperty.Over.homMk
    (pullback.lift (f := 𝟙 Y) (g := f) f (𝟙 X)
      ((Category.comp_id f).trans (Category.id_comp f).symm))
    (pullback.lift_snd _ _ _)

/-- Restriction of sections is the adjunction unit followed by restriction along the canonical map of terminal étale objects. -/
def sectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sections Y ⟶ inverseImage f ⋙ sections X where
  app F :=
    (sections Y).map
      ((Etale.Abelian.adjunction f).unit.app F) ≫
      (CategoryTheory.SiteAbelianSectionsDerived.sectionsIso.{u + 1, u, u + 1, u, u + 1}
        (JC := Y.smallEtaleTopology) (JD := X.smallEtaleTopology)
        (smallEtalePullback f) (unitObject Y)).hom.app ((inverseImage f).obj F) ≫
      ((inverseImage f).obj F).obj.map (unitToPullback f).op
  naturality := sorry

/-- Derived restriction is induced from the adjunction-unit map by the right-derived universal property. -/
def derivedSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedSections Y ⟶ derivedInverseImage f ⋙ derivedSections X :=
  (derivedSections Y).rightDerivedDesc (Cochain.unit (sections Y))
    (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ)) _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (sectionsPullback f) (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
        DerivedCategory AddCommGrpCat.{u + 1}) ≫
      Cochain.ExactFirst.unit (ExactFunctor.of (inverseImage f)) (sections X))

/-- On cochain complexes derived restriction is induced by the underived map and the canonical right-derived comparison. -/
theorem derivedSectionsPullback_fac {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Cochain.unit (sections Y) ≫
      Functor.whiskerLeft (DerivedCategory.Q : CochainComplex (Coefficients Y) ℤ ⥤ _)
        (derivedSectionsPullback f) =
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (sectionsPullback f) (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
        DerivedCategory AddCommGrpCat.{u + 1}) ≫
      Cochain.ExactFirst.unit (ExactFunctor.of (inverseImage f)) (sections X) := by
  exact Functor.rightDerived_fac _ _ _ _ _

/-- A morphism between chosen strict henselization schemes is compatible with the structural maps to the base. -/
abbrev InducedStrictHenselizationTriangle {X S : Scheme.{u}} {RshS RshX : Type u}
    (f : X ⟶ S) (xbar : GeometricPoint X)
    [CommRing RshS]
    [Algebra (S.presheaf.stalk (xbar.map f).image) RshS]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (xbar.map f).image) RshS]
    [CommRing RshX] [Algebra (X.presheaf.stalk xbar.image) RshX]
    [IsStrictHenselizationOf (X.presheaf.stalk xbar.image) RshX]
    (h : strictHenselizationScheme X xbar RshX ⟶
      strictHenselizationScheme S (xbar.map f) RshS) : Prop :=
  h ≫ strictHenselizationMap S (xbar.map f) RshS =
    strictHenselizationMap X xbar RshX ≫ f

/-- The derived comparison morphism for arbitrary strict-henselization presentations and an over-base morphism. -/
def etaleCohomologyAlpha
    {X S : Scheme.{u}} {RshS RshX : Type u}
    (f : X ⟶ S) (xbar : GeometricPoint X)
    [CommRing RshS]
    [Algebra (S.presheaf.stalk (xbar.map f).image) RshS]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (xbar.map f).image) RshS]
    [CommRing RshX] [Algebra (X.presheaf.stalk xbar.image) RshX]
    [IsStrictHenselizationOf (X.presheaf.stalk xbar.image) RshX]
    (h : strictHenselizationScheme X xbar RshX ⟶
      strictHenselizationScheme S (xbar.map f) RshS)
    (h_induced : InducedStrictHenselizationTriangle f xbar h)
    (tbar : GeometricPoint
      (strictHenselizationScheme S (xbar.map f) RshS))
    (K : Complexes X) :
    (derivedSections (strictHenselizationScheme X xbar RshX)).obj
        ((derivedInverseImage (strictHenselizationMap X xbar RshX)).obj K) ⟶
      (derivedSections (pullback tbar.hom h)).obj
        ((derivedInverseImage (pullback.snd tbar.hom h)).obj
          ((derivedInverseImage (strictHenselizationMap X xbar RshX)).obj K)) :=
  (derivedSectionsPullback (pullback.snd tbar.hom h)).app
    ((derivedInverseImage (strictHenselizationMap X xbar RshX)).obj K)

/-- The canonical derived comparison attached to a morphism, a geometric point, and a point of the intrinsic strict henselization. -/
def alpha
    {X S : Scheme.{u}} (f : X ⟶ S) (xbar : GeometricPoint X)
    (tbar : GeometricPoint (strictHenselizationAt S (xbar.map f)))
    (K : Complexes X) :
    (derivedSections (strictHenselizationAt X xbar)).obj
        ((derivedInverseImage (StrictHenselization.toScheme X xbar)).obj K) ⟶
      (derivedSections
        (pullback tbar.hom (StrictHenselization.map f xbar))).obj
        ((derivedInverseImage
          (pullback.snd tbar.hom (StrictHenselization.map f xbar))).obj
          ((derivedInverseImage (StrictHenselization.toScheme X xbar)).obj K)) :=
  (derivedSectionsPullback
      (pullback.snd tbar.hom (StrictHenselization.map f xbar))).app
    ((derivedInverseImage (StrictHenselization.toScheme X xbar)).obj K)

end AlgebraicGeometry.Scheme.EtaleVanishingCycles
