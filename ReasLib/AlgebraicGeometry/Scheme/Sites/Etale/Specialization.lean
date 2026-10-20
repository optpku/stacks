/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselianSections

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u v w

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Transport sections pullback between supplied stalk-to-sections equivalences.
This operation depends on the supplied comparison and identifications. -/
noncomputable def étaleSpecializationMap
    (S : Scheme.{u}) (sbar tbar : Scheme.GeometricPoint S)
    (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology (Type u)]
    [HasWeakSheafify (strictHenselizationScheme S tbar RshT).smallEtaleTopology (Type u)]
    (c : strictHenselizationScheme S tbar RshT ⟶
      strictHenselizationScheme S sbar RshS)
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S tbar RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c).op.HasLeftKanExtension P]
    (hc_over :
      c ≫ strictHenselizationMap S sbar RshS =
        strictHenselizationMap S tbar RshT)
    (F : Sheaf S.smallEtaleTopology (Type u))
    (eS :
      Scheme.Etale.stalk sbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F))
    (ePull :
      (((smallEtalePullback c).sheafPullback (Type u)
          (strictHenselizationScheme S sbar RshS).smallEtaleTopology
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F)).obj.obj
        (op ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F))
    (eT :
      Scheme.Etale.stalk tbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F)) :
    Scheme.Etale.stalk sbar F.obj → Scheme.Etale.stalk tbar F.obj :=
  fun x ↦
    eT.symm
      (ePull
        ((fun _ ↦
            etaleSectionsPullback c
              (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
                  S.smallEtaleTopology
                  (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F)
              (eS x))
          hc_over))

/-- The conditional stalk transport is sections pullback conjugated by the supplied
stalk-to-sections equivalences. -/
theorem étaleSpecializationMap_apply
    (S : Scheme.{u}) (sbar tbar : Scheme.GeometricPoint S)
    (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology (Type u)]
    [HasWeakSheafify (strictHenselizationScheme S tbar RshT).smallEtaleTopology (Type u)]
    (c : strictHenselizationScheme S tbar RshT ⟶
      strictHenselizationScheme S sbar RshS)
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S tbar RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c).op.HasLeftKanExtension P]
    (hc_over :
      c ≫ strictHenselizationMap S sbar RshS =
        strictHenselizationMap S tbar RshT)
    (F : Sheaf S.smallEtaleTopology (Type u))
    (eS :
      Scheme.Etale.stalk sbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F))
    (ePull :
      (((smallEtalePullback c).sheafPullback (Type u)
          (strictHenselizationScheme S sbar RshS).smallEtaleTopology
          (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj
          (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F)).obj.obj
        (op ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F))
    (eT :
      Scheme.Etale.stalk tbar F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S tbar RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S tbar RshT).smallEtaleTopology).obj F))
    (x : Scheme.Etale.stalk sbar F.obj) :
    étaleSpecializationMap S sbar tbar RshS RshT c hc_over F eS ePull eT x =
      eT.symm
        (ePull
          (etaleSectionsPullback c
            (((smallEtalePullback (strictHenselizationMap S sbar RshS)).sheafPullback (Type u)
                S.smallEtaleTopology
                (strictHenselizationScheme S sbar RshS).smallEtaleTopology).obj F)
            (eS x))) := sorry


/-- Geometric specialization on a normalized neighborhood agrees with Kan-model
sections pullback along a compatible over-base comparison. -/
theorem StrictHenselianNeighborhood.specialization_eq_sectionsPullback
    (A : Type w) [Category.{v} A]
    [HasColimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u} A]
    {S X Y : Scheme.{u}} {s t : GeometricPoint S} {p : X ⟶ S} {q : Y ⟶ S}
    (source : StrictHenselianNeighborhood s p) (target : StrictHenselianNeighborhood t q)
    (point : Spec (.of t.K) ⟶ X) (point_over : point ≫ p = t.hom)
    (comparison : Y ⟶ X) (comparison_over : comparison ≫ p = q)
    (comparison_point : target.closedPoint ≫ comparison = point)
    (F : Sheaf S.smallEtaleTopology A) :
    ((source.specializationPoint point point_over).sheafFiber).app F ≫
        (target.stalkSectionsIso A).hom.app F =
      (source.stalkSectionsIso A).hom.app F ≫
        (strictHenselianSectionsPullback A comparison comparison_over).app F := sorry

/-- Ordinary geometric specialization is pullback of genuine sections along the
canonical comparison of strict henselizations, through the closed-point germ maps. -/
theorem etaleSpecialization_eq_strictHenselianPullback {S : Scheme.{u}}
    (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    (strictHenselianGlobalToStalk (Type (u + 1)) s).app F ≫
        (((StrictHenselianNeighborhood.canonical s).specializationPoint
          point point_over).sheafFiber).app F =
      (strictHenselianGlobalSectionsPullback (Type (u + 1)) s t
        (StrictHenselization.comparison s t point point_over)
        (StrictHenselization.comparison_over s t point point_over)).app F ≫
        (strictHenselianGlobalToStalk (Type (u + 1)) t).app F := sorry

end AlgebraicGeometry.Scheme

end
