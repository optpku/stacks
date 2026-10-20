module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The `RΓ`-level pullback of abelian sections along a scheme morphism. -/
noncomputable def derivedEtaleSectionsPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [(ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))).obj.PreservesInjectiveObjects]
    [Functor.Additive (siteAbelianSectionsFunctor Y.smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))]
    [Functor.Additive (siteAbelianSectionsFunctor X.smallEtaleTopology
        ((smallEtalePullback f).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance) ⋙
        siteAbelianSectionsFunctor X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))]
    (G : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})) :
    (siteAbelianSectionsDerived Y.smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)).obj G ⟶
      (siteAbelianSectionsDerived X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))).obj
        (((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)).mapDerivedCategory.obj G) :=
  (Functor.RightDerived.mapNatTrans
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex
          (etaleAbelianSectionsPullbackNatTrans f) (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex AddCommGrpCat.{u} ℤ ⥤
            DerivedCategory AddCommGrpCat.{u}))).app G ≫
    (Functor.RightDerived.Cochain.ExactFirst.iso
        (ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)))
        (siteAbelianSectionsFunctor X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))).inv.app G

/-- The `RΓ`-pullback is the derived adjunction-unit comparison along `f`. -/
theorem derivedEtaleSectionsPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteLimits ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [PreservesFiniteColimits ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))]
    [(ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance))).obj.PreservesInjectiveObjects]
    [Functor.Additive (siteAbelianSectionsFunctor Y.smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))]
    [Functor.Additive (siteAbelianSectionsFunctor X.smallEtaleTopology
        ((smallEtalePullback f).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))]
    [Functor.Additive ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance) ⋙
        siteAbelianSectionsFunctor X.smallEtaleTopology
          ((smallEtalePullback f).obj
            (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))]
    (G : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})) :
    derivedEtaleSectionsPullback f G =
      (Functor.RightDerived.mapNatTrans
          (DerivedCategory.Q :
            CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
              DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))
          (HomologicalComplex.quasiIso
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))
          (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex
              (etaleAbelianSectionsPullbackNatTrans f) (ComplexShape.up ℤ))
            (DerivedCategory.Q :
              CochainComplex AddCommGrpCat.{u} ℤ ⥤
                DerivedCategory AddCommGrpCat.{u}))).app G ≫
        (Functor.RightDerived.Cochain.ExactFirst.iso
            (ExactFunctor.of ((@Sheaf.smallEtaleInverseImage _ _ f AddCommGrpCat.{u} inferInstance
      (HasSheafify.isRightAdjoint (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u}))
      inferInstance)))
            (siteAbelianSectionsFunctor X.smallEtaleTopology
              ((smallEtalePullback f).obj
                (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))).inv.app G := sorry


end AlgebraicGeometry.Scheme

end
