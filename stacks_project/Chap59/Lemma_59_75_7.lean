module

public import stacks_project.Chap59.Theorem_59_53_1
public import stacks_project.Chap59.Remark_59_75_2_Yet_another_description_of_sp_Comparison
public import stacks_project.Chap59.Remark_59_75_2_Yet_another_description_of_sp_Map

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (sbar : GeometricPoint S)
variable (RshS : Type u) [CommRing RshS]
variable [Algebra (S.presheaf.stalk sbar.image) RshS]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar RshS))

/-- The geometric point of `S` obtained by composing `t̄` with the
strict-henselization map `Spec(O^{sh}_{S,s̄}) ⟶ S`. -/
def imageGeometricPoint : GeometricPoint S :=
  GeometricPoint.of tbar.K (tbar.hom ≫ strictHenselizationMap S sbar RshS)

variable (RshT : Type u) [CommRing RshT]
variable [Algebra (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
variable [IsStrictHenselizationOf
  (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
variable (c :
  strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT ⟶
    strictHenselizationScheme S sbar RshS)
variable (hc_over :
  c ≫ strictHenselizationMap S sbar RshS =
    strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)

/-- The fibre-product morphism `id_X × c : X ×_S Spec(O^{sh}_{S,t̄}) ⟶
X ×_S Spec(O^{sh}_{S,s̄})` over `f` and the Remark 59.75.2 comparison `c`. -/
def idXTimesC :
    henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT ⟶
      henselizedFiber f sbar RshS :=
  pullback.map f
    (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
    f (strictHenselizationMap S sbar RshS) (𝟙 X) c (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id
        (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)).trans
      hc_over.symm)

/-- The first projection of `id_X × c` is the identity on `X`. -/
theorem idXTimesC_fst :
    idXTimesC f sbar RshS tbar RshT c hc_over ≫
        henselizedFiberToX f sbar RshS =
      henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT := sorry

/-- The second projection of `id_X × c` is the comparison morphism `c`. -/
theorem idXTimesC_snd :
    idXTimesC f sbar RshS tbar RshT c hc_over ≫
        pullback.snd f (strictHenselizationMap S sbar RshS) =
      pullback.snd f
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT) ≫
        c := sorry

variable [QuasiCompact f] [QuasiSeparated f]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (henselizedFiber f sbar RshS).smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasWeakSheafify
  (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasExt (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology
  AddCommGrpCat.{u})]
variable [HasExt
  (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [(etaleAbelianPushforward f).Additive]
variable [((smallEtalePullback (henselizedFiberToX f sbar RshS)).sheafPushforwardContinuous
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f sbar RshS).smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).sheafPushforwardContinuous
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback (henselizedFiberToX f sbar RshS)).sheafPullback
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f sbar RshS).smallEtaleTopology).Additive]
variable [((smallEtalePullback
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).sheafPullback
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback (henselizedFiberToX f sbar RshS)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f sbar RshS).smallEtaleTopology)]
variable [PreservesFiniteLimits
    ((smallEtalePullback
        (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).sheafPullback
      AddCommGrpCat.{u} X.smallEtaleTopology
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback (henselizedFiberToX f sbar RshS)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f sbar RshS).smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback
        (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).sheafPullback
      AddCommGrpCat.{u} X.smallEtaleTopology
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology)]
variable [(sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (pointSmallEtale sbar.hom).presheafFiber).Additive]
variable [(sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (pointSmallEtale (imageGeometricPoint sbar RshS tbar).hom).presheafFiber).Additive]
variable [PreservesFiniteLimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale sbar.hom).presheafFiber)]
variable [PreservesFiniteLimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale (imageGeometricPoint sbar RshS tbar).hom).presheafFiber)]
variable [PreservesFiniteColimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale sbar.hom).presheafFiber)]
variable [PreservesFiniteColimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale (imageGeometricPoint sbar RshS tbar).hom).presheafFiber)]
variable [IsGrothendieckAbelian
    (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
    (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
      AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor (henselizedFiber f sbar RshS).smallEtaleTopology
    (globalEtale (henselizedFiber f sbar RshS))).Additive]
variable [(siteAbelianSectionsFunctor
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    (globalEtale (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor (henselizedFiber f sbar RshS).smallEtaleTopology
        (globalEtale (henselizedFiber f sbar RshS))))
    (HomologicalComplex.quasiIso
      (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor
        (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
        (globalEtale (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))))
    (HomologicalComplex.quasiIso
      (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
        AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]

variable [HasSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify
  (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
  AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
  AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (strictHenselizationScheme S sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)).op.HasLeftKanExtension P]
variable [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback c).op.HasLeftKanExtension P]
variable [∀ P : (henselizedFiber f sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).op.HasLeftKanExtension P]
variable [(Sheaf.smallEtaleInverseImage (strictHenselizationMap S sbar RshS)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (strictHenselizationMap S sbar RshS) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
      AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u})]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u})]
variable [(ExactFunctor.of (Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
variable [(Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over) AddCommGrpCat.{u})]
variable [(ExactFunctor.of
      (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
        AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
variable [(siteAbelianSectionsFunctor
    (strictHenselizationScheme S sbar RshS).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
      inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor
    (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    ((smallEtalePullback c).obj
      (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
        inferInstance))).Additive]
variable [(Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u} ⋙
    siteAbelianSectionsFunctor
      (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
      ((smallEtalePullback c).obj
        (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
          inferInstance))).Additive]
variable [(siteAbelianSectionsFunctor (henselizedFiber f sbar RshS).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
      (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))).Additive]
variable [(Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
      AddCommGrpCat.{u} ⋙
    siteAbelianSectionsFunctor
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
      ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
        (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
          inferInstance))).Additive]

variable [((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).sheafPullback
    AddCommGrpCat.{u} (henselizedFiber f sbar RshS).smallEtaleTopology
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).sheafPullback
      AddCommGrpCat.{u} (henselizedFiber f sbar RshS).smallEtaleTopology
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).sheafPullback
      AddCommGrpCat.{u} (henselizedFiber f sbar RshS).smallEtaleTopology
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology)]

variable (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))

/-- Derived inverse image along `id_X × c`. -/
noncomputable def idXTimesC_derivedPullback :
    DerivedCategory
        (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory
        (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          AddCommGrpCat.{u}) :=
  ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).sheafPullback
      AddCommGrpCat.{u} (henselizedFiber f sbar RshS).smallEtaleTopology
      (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology).mapDerivedCategory

/-- `RΓ`-pullback of `p⁻¹ K` along `id_X × c`. -/
noncomputable def idXTimesC_derivedSectionsPullback :
    (siteAbelianSectionsDerived (henselizedFiber f sbar RshS).smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance)).obj
      (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K)) ⟶
      (siteAbelianSectionsDerived
          (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
            (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
              inferInstance))).obj
        ((Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))) :=
  derivedEtaleSectionsPullback (idXTimesC f sbar RshS tbar RshT c hc_over)
    (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))

/-- The bottom arrow is `derivedEtaleSectionsPullback` along `id_X × c`. -/
theorem idXTimesC_derivedSectionsPullback_eq :
    idXTimesC_derivedSectionsPullback f sbar RshS tbar RshT c hc_over K =
      derivedEtaleSectionsPullback (idXTimesC f sbar RshS tbar RshT c hc_over)
        (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K)) := sorry

/-- Specialization of `Rf_* K` along `s̄ ⇝ t̄`, as `derivedSpecializationMap`. -/
noncomputable def derivedPushforward_specializationMap
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _
                (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).obj
          ((Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u}).mapDerivedCategory.obj
            ((Sheaf.smallEtaleInverseImage
                (strictHenselizationMap S sbar RshS)
                AddCommGrpCat.{u}).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj
                ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))) ≅
        (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
              inferInstance)).obj
          ((Sheaf.smallEtaleInverseImage
              (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
              AddCommGrpCat.{u}).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj
              ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))) :
    (siteAbelianSectionsDerived
          (strictHenselizationScheme S sbar RshS).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)).obj
        ((Sheaf.smallEtaleInverseImage
            (strictHenselizationMap S sbar RshS)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj
            ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))) ⟶
      (siteAbelianSectionsDerived
          (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
            inferInstance)).obj
        ((Sheaf.smallEtaleInverseImage
            (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj
            ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))) :=
  derivedSpecializationMap S sbar (imageGeometricPoint sbar RshS tbar) RshS RshT c
    hc_over
    (DerivedCategory.Plus.ι.obj
      ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))
    ePull

/-- The specialization of `Rf_* K` is `derivedSpecializationMap`. -/
theorem derivedPushforward_specializationMap_eq
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _
                (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).obj
          ((Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u}).mapDerivedCategory.obj
            ((Sheaf.smallEtaleInverseImage
                (strictHenselizationMap S sbar RshS)
                AddCommGrpCat.{u}).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj
                ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))) ≅
        (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
              inferInstance)).obj
          ((Sheaf.smallEtaleInverseImage
              (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
              AddCommGrpCat.{u}).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj
              ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))) :
    derivedPushforward_specializationMap f sbar RshS tbar RshT c hc_over K ePull =
      derivedSpecializationMap S sbar (imageGeometricPoint sbar RshS tbar) RshS RshT c
        hc_over
        (DerivedCategory.Plus.ι.obj
          ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))
        ePull := sorry

/-- Derived stalk of `Rf_* K` at `s̄`. -/
abbrev derivedPushforward_stalkS : DerivedCategory AddCommGrpCat.{u} :=
  (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale sbar.hom).presheafFiber).mapDerivedCategory.obj
    (DerivedCategory.Plus.ι.obj
      ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))

/-- Derived stalk of `Rf_* K` at the image of `t̄`. -/
abbrev derivedPushforward_stalkT : DerivedCategory AddCommGrpCat.{u} :=
  (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (pointSmallEtale (imageGeometricPoint sbar RshS tbar).hom).presheafFiber).mapDerivedCategory.obj
    (DerivedCategory.Plus.ι.obj
      ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))

/-- Derived étale global sections of `p⁻¹ K` on the henselized fibre over `s̄`. -/
abbrev derivedPushforward_henselizedSectionsS : DerivedCategory AddCommGrpCat.{u} :=
  (henselizedDerivedGlobalSections f sbar RshS).obj
    (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))

/-- Derived étale global sections of `p⁻¹ K` on the henselized fibre over the image of `t̄`. -/
abbrev derivedPushforward_henselizedSectionsT : DerivedCategory AddCommGrpCat.{u} :=
  (henselizedDerivedGlobalSections f (imageGeometricPoint sbar RshS tbar) RshT).obj
    (henselizedDerivedPullback f (imageGeometricPoint sbar RshS tbar) RshT
      (DerivedCategory.Plus.ι.obj K))

/-- Derived global sections of the inverse image of `Rf_* K` on `Spec(O^{sh}_{S,s̄})`. -/
abbrev derivedPushforward_strictHenselizationSectionsS :
    DerivedCategory AddCommGrpCat.{u} :=
  (siteAbelianSectionsDerived
        (strictHenselizationScheme S sbar RshS).smallEtaleTopology
        (MorphismProperty.Over.mk _
          (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)).obj
      ((Sheaf.smallEtaleInverseImage
          (strictHenselizationMap S sbar RshS)
          AddCommGrpCat.{u}).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))

/-- Derived global sections of the inverse image of `Rf_* K` on `Spec(O^{sh}_{S,t̄})`. -/
abbrev derivedPushforward_strictHenselizationSectionsT :
    DerivedCategory AddCommGrpCat.{u} :=
  (siteAbelianSectionsDerived
        (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
        (MorphismProperty.Over.mk _
          (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
          inferInstance)).obj
      ((Sheaf.smallEtaleInverseImage
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
          AddCommGrpCat.{u}).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))

/-- Theorem 59.53.1 (3) identifies the derived stalk of `Rf_* K` at `s̄`
with derived global sections of `p⁻¹ K` on the henselized fibre. -/
theorem derivedPushforward_stalk_eq_henselizedSectionsS :
    IsIsomorphic (derivedPushforward_stalkS f sbar K)
      (derivedPushforward_henselizedSectionsS f sbar RshS K) := sorry

/-- Theorem 59.53.1 (3) identifies the derived stalk of `Rf_* K` at the
image of `t̄` with derived global sections of `p⁻¹ K` on that henselized fibre. -/
theorem derivedPushforward_stalk_eq_henselizedSectionsT :
    IsIsomorphic (derivedPushforward_stalkT f sbar RshS tbar K)
      (derivedPushforward_henselizedSectionsT f sbar RshS tbar RshT K) := sorry

/-- Remark 59.75.1 identifies the derived stalk of `Rf_* K` at `s̄` with derived
sections on `Spec(O^{sh}_{S,s̄})`. -/
theorem derivedPushforward_stalk_eq_strictHenselizationSectionsS :
    IsIsomorphic (derivedPushforward_stalkS f sbar K)
      (derivedPushforward_strictHenselizationSectionsS f sbar RshS K) := sorry

/-- Remark 59.75.1 identifies the derived stalk of `Rf_* K` at the image of `t̄`
with derived sections on `Spec(O^{sh}_{S,t̄})`. -/
theorem derivedPushforward_stalk_eq_strictHenselizationSectionsT :
    IsIsomorphic (derivedPushforward_stalkT f sbar RshS tbar K)
      (derivedPushforward_strictHenselizationSectionsT f sbar RshS tbar RshT K) := sorry

/-- The henselized-fibre `RΓ` used by Theorem 59.53.1 agrees with the identity-site
`RΓ` that receives the bottom arrow at `s̄`. -/
theorem derivedPushforward_henselizedSections_eq_siteSectionsS :
    IsIsomorphic (derivedPushforward_henselizedSectionsS f sbar RshS K)
      ((siteAbelianSectionsDerived (henselizedFiber f sbar RshS).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
            inferInstance)).obj
        (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))) := sorry

/-- Pullback of `p⁻¹ K` along `id_X × c` is identified with `p⁻¹ K` on the
henselized fibre over the image of `t̄`. -/
theorem derivedPushforward_idXTimesC_sections_eq_henselizedSectionsT :
    IsIsomorphic
      ((siteAbelianSectionsDerived
            (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
              (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
                inferInstance))).obj
          ((Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
              AddCommGrpCat.{u}).mapDerivedCategory.obj
            (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))))
      (derivedPushforward_henselizedSectionsT f sbar RshS tbar RshT K) := sorry

/-- Lemma 59.75.7: for a quasi-compact quasi-separated morphism `f : X ⟶ S`,
`K ∈ D⁺(X_étale)`, a geometric point `s̄` of `S`, and a geometric point `t̄` of
`Spec(O^{sh}_{S,s̄})`, the specialization map of
`Rf_* K` from `s̄` to the image of `t̄` in `S` commutes with `RΓ`-pullback of
`p⁻¹ K` along `id_X × c`, where `c` is the Remark 59.75.2 comparison
`Spec(O^{sh}_{S,t̄}) ⟶ Spec(O^{sh}_{S,s̄})`. The vertical arrows are the
identifications of Theorem 59.53.1 (3). -/
@[stacks 0GJ8]
theorem derivedPushforward_specialization_commSq
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _
                (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).obj
          ((Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u}).mapDerivedCategory.obj
            ((Sheaf.smallEtaleInverseImage
                (strictHenselizationMap S sbar RshS)
                AddCommGrpCat.{u}).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj
                ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))) ≅
        (derivedPushforward_strictHenselizationSectionsT f sbar RshS tbar RshT K)) :
    ∃ (isoS :
          derivedPushforward_stalkS f sbar K ≅
            derivedPushforward_henselizedSectionsS f sbar RshS K)
      (isoT :
          derivedPushforward_stalkT f sbar RshS tbar K ≅
            derivedPushforward_henselizedSectionsT f sbar RshS tbar RshT K)
      (eStalkS :
          derivedPushforward_stalkS f sbar K ≅
            derivedPushforward_strictHenselizationSectionsS f sbar RshS K)
      (eStalkT :
          derivedPushforward_stalkT f sbar RshS tbar K ≅
            derivedPushforward_strictHenselizationSectionsT f sbar RshS tbar RshT K)
      (eBotS :
          derivedPushforward_henselizedSectionsS f sbar RshS K ≅
            (siteAbelianSectionsDerived (henselizedFiber f sbar RshS).smallEtaleTopology
                (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
                  inferInstance)).obj
              (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K)))
      (eBotT :
          (siteAbelianSectionsDerived
                (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
                ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
                  (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
                    inferInstance))).obj
              ((Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
                  AddCommGrpCat.{u}).mapDerivedCategory.obj
                (henselizedDerivedPullback f sbar RshS (DerivedCategory.Plus.ι.obj K))) ≅
            derivedPushforward_henselizedSectionsT f sbar RshS tbar RshT K),
      CommSq
        (eStalkS.hom ≫
          derivedPushforward_specializationMap f sbar RshS tbar RshT c hc_over K ePull ≫
            eStalkT.inv)
        isoS.hom isoT.hom
        (eBotS.hom ≫
          idXTimesC_derivedSectionsPullback f sbar RshS tbar RshT c hc_over K ≫
            eBotT.hom) := sorry

end AlgebraicGeometry.Scheme.Etale

end
