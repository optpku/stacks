/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import Mathlib.Algebra.Category.Grp.AB

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Transport derived sections pullback through a supplied inverse-image comparison.
The operation is conditional on that comparison and the indicated derived-functor
hypotheses. -/
noncomputable def derivedSpecializationMap
    (S : Scheme.{u}) (sbar tbar : Scheme.GeometricPoint S)
    (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasSheafify (strictHenselizationScheme S tbar RshT).smallEtaleTopology
      AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (strictHenselizationScheme S sbar RshS).smallEtaleTopology
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (strictHenselizationScheme S tbar RshT).smallEtaleTopology
        AddCommGrpCat.{u})]
    (c : strictHenselizationScheme S tbar RshT ⟶
      strictHenselizationScheme S sbar RshS)
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (strictHenselizationMap S tbar RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback c).op.HasLeftKanExtension P]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [(ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))).obj.PreservesInjectiveObjects]
    [Functor.Additive (siteAbelianSectionsFunctor
        (strictHenselizationScheme S sbar RshS).smallEtaleTopology
        (MorphismProperty.Over.mk _
          (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))]
    [Functor.Additive (siteAbelianSectionsFunctor
        (strictHenselizationScheme S tbar RshT).smallEtaleTopology
        ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance) ⋙
        siteAbelianSectionsFunctor
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology
          ((smallEtalePullback c).obj
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)))]
    (hc_over :
      c ≫ strictHenselizationMap S sbar RshS =
        strictHenselizationMap S tbar RshT)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S tbar RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _
                (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).obj
          (((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj
            (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K)) ≅
        (siteAbelianSectionsDerived
            (strictHenselizationScheme S tbar RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S tbar RshT)) inferInstance)).obj
          (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K)) :
    (siteAbelianSectionsDerived
          (strictHenselizationScheme S sbar RshS).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)).obj
        (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K) ⟶
      (siteAbelianSectionsDerived
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S tbar RshT)) inferInstance)).obj
        (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K) :=
  (fun _ ↦
      derivedEtaleSectionsPullback c
          (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K) ≫
        ePull.hom)
    hc_over

/-- The conditional derived transport is sections pullback followed by the supplied
inverse-image comparison. -/
theorem derivedSpecializationMap_eq_sectionsPullback
    (S : Scheme.{u}) (sbar tbar : Scheme.GeometricPoint S)
    (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasSheafify (strictHenselizationScheme S tbar RshT).smallEtaleTopology
      AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (strictHenselizationScheme S sbar RshS).smallEtaleTopology
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (strictHenselizationScheme S tbar RshT).smallEtaleTopology
        AddCommGrpCat.{u})]
    (c : strictHenselizationScheme S tbar RshT ⟶
      strictHenselizationScheme S sbar RshS)
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (strictHenselizationMap S tbar RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback c).op.HasLeftKanExtension P]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits
      ((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [(ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))).obj.PreservesInjectiveObjects]
    [Functor.Additive (siteAbelianSectionsFunctor
        (strictHenselizationScheme S sbar RshS).smallEtaleTopology
        (MorphismProperty.Over.mk _
          (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))]
    [Functor.Additive (siteAbelianSectionsFunctor
        (strictHenselizationScheme S tbar RshT).smallEtaleTopology
        ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance) ⋙
        siteAbelianSectionsFunctor
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology
          ((smallEtalePullback c).obj
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)))]
    (hc_over :
      c ≫ strictHenselizationMap S sbar RshS =
        strictHenselizationMap S tbar RshT)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S tbar RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _
                (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).obj
          (((@Sheaf.smallEtaleInverseImage _ _ c AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj
            (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K)) ≅
        (siteAbelianSectionsDerived
            (strictHenselizationScheme S tbar RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S tbar RshT)) inferInstance)).obj
          (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S tbar RshT) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S tbar RshT).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K)) :
    derivedSpecializationMap S sbar tbar RshS RshT c hc_over K ePull =
      derivedEtaleSectionsPullback c
          (((@Sheaf.smallEtaleInverseImage _ _ (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := (strictHenselizationScheme S sbar RshS).smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj K) ≫
        ePull.hom := sorry

section ExactSections

variable {S : Scheme.{u}}
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The geometric stalk as a bundled exact functor on abelian étale sheaves. -/
def etaleStalkExact (s : GeometricPoint S) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ AddCommGrpCat.{u + 1} :=
  ⟨s.toSmallEtalePoint.sheafFiber,
    ⟨@GrothendieckTopology.Point.instPreservesFiniteLimitsSheafSheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize
        S.Etale inferInstance S.smallEtaleTopology s.toSmallEtalePoint
        AddCommGrpCat.{u + 1} inferInstance inferInstance (locallySmall_self S.Etale) inferInstance
        (AB5OfSize_shrink.{u, u, u + 1, u + 1} AddCommGrpCat.{u + 1}),
      (inferInstance : PreservesFiniteColimits
        (s.toSmallEtalePoint.sheafFiber (A := AddCommGrpCat.{u + 1})))⟩⟩

/-- Kan-model sections on a normalized strict-henselian neighborhood preserve finite limits. -/
theorem strictHenselianSections_preservesFiniteLimits {X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p) :
    PreservesFiniteLimits (strictHenselianSections AddCommGrpCat.{u + 1} p) := sorry

/-- Kan-model sections on a normalized strict-henselian neighborhood preserve finite colimits. -/
theorem strictHenselianSections_preservesFiniteColimits {X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p) :
    PreservesFiniteColimits (strictHenselianSections AddCommGrpCat.{u + 1} p) := sorry

/-- Kan-model sections bundled with the exactness supplied by normalized neighborhood lifts. -/
def strictHenselianSectionsExact {X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ AddCommGrpCat.{u + 1} :=
  ⟨strictHenselianSections AddCommGrpCat.{u + 1} p,
    ⟨strictHenselianSections_preservesFiniteLimits neighborhood,
      strictHenselianSections_preservesFiniteColimits neighborhood⟩⟩

/-- Unbounded derived Kan-model sections obtained by localizing the exact sections functor. -/
def strictHenselianDerivedSections {X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  (strictHenselianSectionsExact neighborhood).mapDerivedCategory

/-- The stalk-to-Kan-sections isomorphism localized on arbitrary unbounded derived objects. -/
def StrictHenselianNeighborhood.derivedStalkSectionsIso {X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p) :
    (etaleStalkExact s).mapDerivedCategory ≅ strictHenselianDerivedSections neighborhood :=
  ExactFunctor.MapDerivedCategory.mapIso
    (ObjectProperty.isoMk _ (neighborhood.stalkSectionsIso AddCommGrpCat.{u + 1}) :
      etaleStalkExact s ≅ strictHenselianSectionsExact neighborhood)

/-- The localized stalk-to-Kan-sections comparison on a complex is the comparison
of exact functors followed through the localization functor. -/
theorem StrictHenselianNeighborhood.derivedStalkSectionsIso_Q {X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    neighborhood.derivedStalkSectionsIso.hom.app (DerivedCategory.Q.obj K) =
      (etaleStalkExact s).obj.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (ObjectProperty.homMk (neighborhood.stalkSectionsIso AddCommGrpCat.{u + 1}).hom :
              etaleStalkExact s ⟶ strictHenselianSectionsExact neighborhood).hom
            (ComplexShape.up ℤ)).app K) ≫
        (strictHenselianSectionsExact neighborhood).obj.mapDerivedCategoryFactors.inv.app K := sorry

/-- Genuine strict-henselian global sections preserve finite limits of abelian étale sheaves. -/
theorem strictHenselianGlobalSections_preservesFiniteLimits (s : GeometricPoint S) :
    PreservesFiniteLimits ((@strictHenselianGlobalSections AddCommGrpCat.{u + 1} inferInstance inferInstance
      (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s)) := sorry

/-- Genuine strict-henselian global sections preserve finite colimits of abelian étale sheaves. -/
theorem strictHenselianGlobalSections_preservesFiniteColimits (s : GeometricPoint S) :
    PreservesFiniteColimits ((@strictHenselianGlobalSections AddCommGrpCat.{u + 1} inferInstance inferInstance
      (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s)) := sorry

/-- Genuine inverse-image global sections, bundled with their exactness. -/
def strictHenselianGlobalSectionsExact (s : GeometricPoint S) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ AddCommGrpCat.{u + 1} :=
  ⟨(@strictHenselianGlobalSections AddCommGrpCat.{u + 1} inferInstance inferInstance
      (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s),
    ⟨strictHenselianGlobalSections_preservesFiniteLimits s,
      strictHenselianGlobalSections_preservesFiniteColimits s⟩⟩

/-- Unbounded derived genuine global sections formed by exact localization. -/
def strictHenselianDerivedGlobalSections (s : GeometricPoint S) :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  (strictHenselianGlobalSectionsExact s).mapDerivedCategory

/-- The closed-point germ transformation localized to unbounded derived categories. -/
def strictHenselianDerivedGlobalToStalk (s : GeometricPoint S) :
    strictHenselianDerivedGlobalSections s ⟶ (etaleStalkExact s).mapDerivedCategory :=
  ExactFunctor.MapDerivedCategory.map
    (ObjectProperty.homMk ((@strictHenselianGlobalToStalk AddCommGrpCat.{u + 1} inferInstance inferInstance
      inferInstance inferInstance (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s)) :
      strictHenselianGlobalSectionsExact s ⟶ etaleStalkExact s)

/-- On the localization of a complex, the derived closed-point germ is the
termwise germ map conjugated by the localization comparison maps. -/
theorem strictHenselianDerivedGlobalToStalk_Q (s : GeometricPoint S)
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    (strictHenselianDerivedGlobalToStalk s).app (DerivedCategory.Q.obj K) =
      (strictHenselianGlobalSectionsExact s).obj.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ObjectProperty.homMk ((@strictHenselianGlobalToStalk AddCommGrpCat.{u + 1} inferInstance inferInstance
      inferInstance inferInstance (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s)) :
            strictHenselianGlobalSectionsExact s ⟶ etaleStalkExact s).hom
          (ComplexShape.up ℤ)).app K) ≫
        (etaleStalkExact s).obj.mapDerivedCategoryFactors.inv.app K := sorry

/-- Derived closed-point germs identify genuine derived global sections with derived stalks. -/
theorem strictHenselianDerivedGlobalToStalk_isIso (s : GeometricPoint S) :
    IsIso (strictHenselianDerivedGlobalToStalk s) := sorry

/-- For every unbounded derived étale object, geometric specialization agrees with
the localized genuine sections pullback along the canonical strict-henselization comparison. -/
theorem derivedEtaleSpecialization_eq_strictHenselianPullback (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (strictHenselianDerivedGlobalToStalk s).app K ≫
        (ExactFunctor.MapDerivedCategory.map (ObjectProperty.homMk
          ((StrictHenselianNeighborhood.canonical s).specializationPoint
            point point_over).sheafFiber : etaleStalkExact s ⟶ etaleStalkExact t)).app K =
      (ExactFunctor.MapDerivedCategory.map (ObjectProperty.homMk
        (@strictHenselianGlobalSectionsPullback AddCommGrpCat.{u + 1} inferInstance inferInstance
          inferInstance inferInstance (fun T : Scheme.{u} ↦ @HasSheafify.isRightAdjoint _ _ T.smallEtaleTopology AddCommGrpCat.{u + 1} inferInstance
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
          (fun {U} cover ↦ inferInstance) inferInstance inferInstance (fun U ↦ inferInstance))) _ s t
          (StrictHenselization.comparison s t point point_over)
          (StrictHenselization.comparison_over s t point point_over)) :
        strictHenselianGlobalSectionsExact s ⟶ strictHenselianGlobalSectionsExact t)).app K ≫
        (strictHenselianDerivedGlobalToStalk t).app K := sorry

end ExactSections

end AlgebraicGeometry.Scheme

end
