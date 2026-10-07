module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImage
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u v

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Global sections of an étale sheaf of sets at the identity étale object. -/
abbrev etaleGlobalSections {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type v)) : Type v :=
  F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 X) inferInstance))

/-- Sections of an inverse-image étale sheaf at the base change of the identity object. -/
abbrev etalePullbackIdentitySections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v, (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (Type v)) : Type v :=
  ((Sheaf.smallEtaleInverseImage f (Type v)).obj G).obj.obj
    (op ((smallEtalePullback f).obj (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))

/-- Pullback of global sections of an étale sheaf of sets along a scheme morphism,
valued at the base change of the identity étale object. -/
def etaleSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [HasWeakSheafify Y.smallEtaleTopology (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v, (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (Type v)) :
    etaleGlobalSections G →
      (((smallEtalePullback f).sheafPullback (Type v)
          Y.smallEtaleTopology X.smallEtaleTopology).obj G).obj.obj
        (op ((smallEtalePullback f).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))) :=
  fun s ↦
    ((smallEtalePullback f).sheafPushforwardContinuousObjObjIso (Type v)
        (((smallEtalePullback f).sheafPullback (Type v)
            Y.smallEtaleTopology X.smallEtaleTopology).obj G)
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom
      ((((smallEtalePullback f).sheafAdjunctionContinuous
            (Type v) Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
        (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)) s)

/-- The sections-pullback map is the adjunction-unit component at the identity étale object. -/
theorem etaleSectionsPullback_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [HasWeakSheafify Y.smallEtaleTopology (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v, (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology (Type v))
    (s : etaleGlobalSections G) :
    etaleSectionsPullback f G s =
      ((smallEtalePullback f).sheafPushforwardContinuousObjObjIso (Type v)
          (((smallEtalePullback f).sheafPullback (Type v)
              Y.smallEtaleTopology X.smallEtaleTopology).obj G)
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom
        ((((smallEtalePullback f).sheafAdjunctionContinuous
              (Type v) Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
          (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)) s) := sorry
/-- Pullback of abelian global sections along a scheme morphism, as the adjunction-unit
component at the identity étale object. -/
def etaleAbelianSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G).obj
        (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)) ⟶
      (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology).obj G).obj.obj
        (op ((smallEtalePullback f).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))) :=
  ((((smallEtalePullback f).sheafAdjunctionContinuous
          AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
      (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))) ≫
    ((smallEtalePullback f).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u}
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            Y.smallEtaleTopology X.smallEtaleTopology).obj G)
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom

/-- The abelian sections-pullback is the adjunction-unit component at the identity
étale object, transported by the continuous pushforward evaluation iso. -/
theorem etaleAbelianSectionsPullback_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleAbelianSectionsPullback f G =
      ((((smallEtalePullback f).sheafAdjunctionContinuous
            AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).unit.app G).hom.app
        (op (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))) ≫
        ((smallEtalePullback f).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u}
            (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
                Y.smallEtaleTopology X.smallEtaleTopology).obj G)
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom := sorry

/-- Reassociation identifying sections after the adjunction unit with
`pushforward ⋙ sections` evaluated on the inverse image. -/
theorem etaleAbelianSectionsPullback_unit_assoc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (siteAbelianSectionsFunctor Y.smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).obj
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
              Y.smallEtaleTopology X.smallEtaleTopology ⋙
            (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
              Y.smallEtaleTopology X.smallEtaleTopology).obj G) =
      (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
            Y.smallEtaleTopology X.smallEtaleTopology ⋙
          siteAbelianSectionsFunctor Y.smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).obj
        ((Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).obj G)) := sorry

/-- Reassociation identifying sections of the inverse image with the composite
`inverse image ⋙ sections`. -/
theorem etaleAbelianSectionsPullback_target_assoc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (siteAbelianSectionsFunctor X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))).obj
        ((Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).obj G) =
      (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u} ⋙
          siteAbelianSectionsFunctor X.smallEtaleTopology
            ((smallEtalePullback f).obj
              (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))).obj G := sorry

/-- The adjunction-unit construction of abelian sections pullback is natural in the sheaf. -/
theorem etaleAbelianSectionsPullbackNatTrans_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    let sourceSections := siteAbelianSectionsFunctor Y.smallEtaleTopology
      (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)
    let targetSections := Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u} ⋙
      siteAbelianSectionsFunctor X.smallEtaleTopology
        ((smallEtalePullback f).obj (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))
    let pullbackMap (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
      sourceSections.map (((smallEtalePullback f).sheafAdjunctionContinuous
        AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).unit.app G) ≫
      eqToHom (etaleAbelianSectionsPullback_unit_assoc f G) ≫
      (SiteAbelianSectionsDerived.sectionsIso
        (JC := Y.smallEtaleTopology) (JD := X.smallEtaleTopology) (smallEtalePullback f)
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom.app
          ((Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).obj G) ≫
      eqToHom (etaleAbelianSectionsPullback_target_assoc f G)
    ∀ (G H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (morphism : G ⟶ H),
      sourceSections.map morphism ≫ pullbackMap H =
        pullbackMap G ≫ targetSections.map morphism := sorry

/-- Underived natural transformation realizing pullback of abelian global sections
along a scheme morphism, as the adjunction unit followed by `sectionsIso`. -/
def etaleAbelianSectionsPullbackNatTrans {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    siteAbelianSectionsFunctor Y.smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance) ⟶
      Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u} ⋙
        siteAbelianSectionsFunctor X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)) where
  app G :=
    (siteAbelianSectionsFunctor Y.smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).map
      (((smallEtalePullback f).sheafAdjunctionContinuous
          AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).unit.app G) ≫
      eqToHom (etaleAbelianSectionsPullback_unit_assoc f G) ≫
      (SiteAbelianSectionsDerived.sectionsIso
          (JC := Y.smallEtaleTopology) (JD := X.smallEtaleTopology)
          (smallEtalePullback f)
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).hom.app
        ((Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).obj G) ≫
      eqToHom (etaleAbelianSectionsPullback_target_assoc f G)
  naturality G H morphism := etaleAbelianSectionsPullbackNatTrans_naturality f G H morphism


end AlgebraicGeometry.Scheme

end
