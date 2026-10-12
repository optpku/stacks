/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_36_2_Stalk
public import stacks_project.Chap59.Remark_59_75_2_Yet_another_description_of_sp_Map

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme.Etale.Small

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The geometric point of `S'` obtained by composing `t̄'` with the canonical
strict-henselization map `Spec(O^{sh}_{S',s̄'}) ⟶ S'`. -/
def étaleSpecializationMap_inverseImage_tbarS'
    {S' : Scheme.{u}} (sbar' : GeometricPoint S') (Rsh' : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh')) :
    GeometricPoint S' :=
  GeometricPoint.of tbar'.K (tbar'.hom ≫ strictHenselizationMap S' sbar' Rsh')

/-- The geometric point `t̄` of `S` obtained as the image of `t̄'` along
`h : Spec(O^{sh}_{S',s̄'}) ⟶ Spec(O^{sh}_{S,s̄})` followed by the
strict-henselization map of `S`. -/
def étaleSpecializationMap_inverseImage_tbar
    {S' S : Scheme.{u}} (g : S' ⟶ S) (sbar' : GeometricPoint S')
    (Rsh' Rsh : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    [CommRing Rsh]
    [Algebra (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh'))
    (h :
      strictHenselizationScheme S' sbar' Rsh' ⟶
        strictHenselizationScheme S (smallEtaleInverseImage_imagePoint g sbar') Rsh) :
    GeometricPoint S :=
  GeometricPoint.of tbar'.K
    (tbar'.hom ≫ h ≫
      strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh)

/-- The morphism of `étaleSpecializationMap_inverseImage_tbarS'` is `t̄'`
followed by the strict-henselization map of `S'`. -/
theorem étaleSpecializationMap_inverseImage_tbarS'_hom
    {S' : Scheme.{u}} (sbar' : GeometricPoint S') (Rsh' : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh')) :
    (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar').hom =
      tbar'.hom ≫ strictHenselizationMap S' sbar' Rsh' :=
  sorry

/-- The morphism of `étaleSpecializationMap_inverseImage_tbar` is `t̄'`
followed by `h` and then the strict-henselization map of `S`. -/
theorem étaleSpecializationMap_inverseImage_tbar_hom
    {S' S : Scheme.{u}} (g : S' ⟶ S) (sbar' : GeometricPoint S')
    (Rsh' Rsh : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    [CommRing Rsh]
    [Algebra (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh'))
    (h :
      strictHenselizationScheme S' sbar' Rsh' ⟶
        strictHenselizationScheme S (smallEtaleInverseImage_imagePoint g sbar') Rsh) :
    (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).hom =
      tbar'.hom ≫ h ≫
        strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh :=
  sorry

/-- If the induced triangle over `g` commutes, then `t̄ = h(t̄')` agrees with
`g` of the image of `t̄'` in `S'`. -/
theorem étaleSpecializationMap_inverseImage_tbar_eq_image
    {S' S : Scheme.{u}} (g : S' ⟶ S) (sbar' : GeometricPoint S')
    (Rsh' Rsh : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    [CommRing Rsh]
    [Algebra (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh'))
    (h :
      strictHenselizationScheme S' sbar' Rsh' ⟶
        strictHenselizationScheme S (smallEtaleInverseImage_imagePoint g sbar') Rsh)
    (hh :
      h ≫ strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh =
        strictHenselizationMap S' sbar' Rsh' ≫ g) :
    (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).hom =
      tbar'.hom ≫ strictHenselizationMap S' sbar' Rsh' ≫ g :=
  sorry

/-- The geometric point `t̄ = h(t̄')` of `S` agrees with `g` of the image of
`t̄'` in `S'` when the induced triangle over `g` commutes. -/
theorem étaleSpecializationMap_inverseImage_tbar_eq
    {S' S : Scheme.{u}} (g : S' ⟶ S) (sbar' : GeometricPoint S')
    (Rsh' Rsh : Type u)
    [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
    [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
    [CommRing Rsh]
    [Algebra (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    [IsStrictHenselizationOf
      (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
    (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh'))
    (h :
      strictHenselizationScheme S' sbar' Rsh' ⟶
        strictHenselizationScheme S (smallEtaleInverseImage_imagePoint g sbar') Rsh)
    (hh :
      h ≫ strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh =
        strictHenselizationMap S' sbar' Rsh' ≫ g) :
    smallEtaleInverseImage_imagePoint g
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') =
      étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h :=
  sorry

variable {S' S : Scheme.{u}} (g : S' ⟶ S)
variable (sbar' : GeometricPoint S') (Rsh' Rsh : Type u)
variable [CommRing Rsh'] [Algebra (S'.presheaf.stalk sbar'.image) Rsh']
variable [IsStrictHenselizationOf (S'.presheaf.stalk sbar'.image) Rsh']
variable [CommRing Rsh]
variable [Algebra (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
variable [IsStrictHenselizationOf
  (S.presheaf.stalk (smallEtaleInverseImage_imagePoint g sbar').image) Rsh]
variable (tbar' : GeometricPoint (strictHenselizationScheme S' sbar' Rsh'))
variable (h :
  strictHenselizationScheme S' sbar' Rsh' ⟶
    strictHenselizationScheme S (smallEtaleInverseImage_imagePoint g sbar') Rsh)
variable (hh :
  h ≫ strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh =
    strictHenselizationMap S' sbar' Rsh' ≫ g)

/-- Lemma 59.75.4: for `g : S' ⟶ S`, a sheaf `F` on `S` étale, a geometric point
`s̄'` of `S'`, and a geometric point `t̄'` of `Spec(O^{sh}_{S',s̄'})`, the
étale specialization map of `g⁻¹ F` from `s̄'` to the image of `t̄'` in `S'`
equals the étale specialization map of `F` from `s̄ = g(s̄')` to `t̄ = h(t̄')`
after the Lemma 59.36.2 stalk identifications
`(g⁻¹ F)_{s̄'} ≅ F_{s̄}` and `(g⁻¹ F)_{t̄'} ≅ F_{t̄}`. The morphism
`h : Spec(O^{sh}_{S',s̄'}) ⟶ Spec(O^{sh}_{S,s̄})` is the supplied triangle
map over `g`. -/
@[stacks 0GJ6]
theorem étaleSpecializationMap_inverseImage
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S'.smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S
        (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology (Type u)]
    (RshT' RshT : Type u)
    [CommRing RshT']
    [Algebra (S'.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar').image) RshT']
    [IsStrictHenselizationOf (S'.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar').image) RshT']
    [CommRing RshT]
    [Algebra (S.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).image) RshT]
    [HasWeakSheafify
      (strictHenselizationScheme S'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
        RshT').smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S
        (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
        RshT).smallEtaleTopology (Type u)]
    (c' :
      strictHenselizationScheme S'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') RshT' ⟶
        strictHenselizationScheme S' sbar' Rsh')
    (c :
      strictHenselizationScheme S
        (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) RshT ⟶
        strictHenselizationScheme S
          (smallEtaleInverseImage_imagePoint g sbar') Rsh)
    [∀ P : S'.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).op.HasLeftKanExtension P]
    [∀ P : S'.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S'
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
          RshT')).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S' sbar' Rsh').Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c').op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
          Rsh)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
          RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S
        (smallEtaleInverseImage_imagePoint g sbar') Rsh).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback g).op.HasLeftKanExtension P]
    [InitiallySmall
      ((smallEtalePullback g ⋙
        (GeometricPoint.toSmallEtalePoint sbar').fiber).Elements)]
    [InitiallySmall
      ((smallEtalePullback g ⋙
        (GeometricPoint.toSmallEtalePoint
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')).fiber).Elements)]
    [((smallEtalePullback g).sheafPushforwardContinuous (Type u)
        S.smallEtaleTopology S'.smallEtaleTopology).IsRightAdjoint]
    (hc'_over :
      c' ≫ strictHenselizationMap S' sbar' Rsh' =
        strictHenselizationMap S'
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') RshT')
    (hc_over :
      c ≫ strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh =
        strictHenselizationMap S
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) RshT)
    (F : Sheaf S.smallEtaleTopology (Type u))
    (eS' :
      Scheme.Etale.stalk sbar'
          (((smallEtalePullback g).sheafPullback (Type u)
              S.smallEtaleTopology S'.smallEtaleTopology).obj F).obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (ePull' :
      (((smallEtalePullback c').sheafPullback (Type u)
          (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology
          (strictHenselizationScheme S'
            (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
            RshT').smallEtaleTopology).obj
          (((smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F))).obj.obj
        (op ((smallEtalePullback c').obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S' sbar' Rsh')) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (eT' :
      Scheme.Etale.stalk
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
          (((smallEtalePullback g).sheafPullback (Type u)
              S.smallEtaleTopology S'.smallEtaleTopology).obj F).obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (eS :
      Scheme.Etale.stalk (smallEtaleInverseImage_imagePoint g sbar') F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
                Rsh)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology).obj F))
    (ePull :
      (((smallEtalePullback c).sheafPullback (Type u)
          (strictHenselizationScheme S
            (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology
          (strictHenselizationScheme S
            (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
            RshT).smallEtaleTopology).obj
          (((smallEtalePullback
              (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
                Rsh)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology).obj
            F)).obj.obj
        (op ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S
              (smallEtaleInverseImage_imagePoint g sbar') Rsh)) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT).smallEtaleTopology).obj F))
    (eT :
      Scheme.Etale.stalk
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT).smallEtaleTopology).obj F)) :
    Function.comp
      (étaleSpecializationMap_inverseImage_tbar_eq g sbar' Rsh' Rsh tbar' h hh ▸
        (smallEtaleInverseImage_stalkIso g
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') F).hom)
      (étaleSpecializationMap S' sbar'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
        Rsh' RshT' c' hc'_over
        (((smallEtalePullback g).sheafPullback (Type u)
            S.smallEtaleTopology S'.smallEtaleTopology).obj F)
        eS' ePull' eT') =
      Function.comp
        (étaleSpecializationMap S (smallEtaleInverseImage_imagePoint g sbar')
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
          Rsh RshT c hc_over F eS ePull eT)
        (smallEtaleInverseImage_stalkIso g sbar' F).hom :=
  sorry

/-- Pointwise form of the Lemma 59.75.4 commuting square for étale specialization
of inverse-image sheaves. -/
theorem étaleSpecializationMap_inverseImage_apply
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S'.smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S
        (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology (Type u)]
    (RshT' RshT : Type u)
    [CommRing RshT']
    [Algebra (S'.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar').image) RshT']
    [IsStrictHenselizationOf (S'.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar').image) RshT']
    [CommRing RshT]
    [Algebra (S.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk
      (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h).image) RshT]
    [HasWeakSheafify
      (strictHenselizationScheme S'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
        RshT').smallEtaleTopology (Type u)]
    [HasWeakSheafify
      (strictHenselizationScheme S
        (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
        RshT).smallEtaleTopology (Type u)]
    (c' :
      strictHenselizationScheme S'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') RshT' ⟶
        strictHenselizationScheme S' sbar' Rsh')
    (c :
      strictHenselizationScheme S
        (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) RshT ⟶
        strictHenselizationScheme S
          (smallEtaleInverseImage_imagePoint g sbar') Rsh)
    [∀ P : S'.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).op.HasLeftKanExtension P]
    [∀ P : S'.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S'
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
          RshT')).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S' sbar' Rsh').Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c').op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
          Rsh)).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback
        (strictHenselizationMap S
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
          RshT)).op.HasLeftKanExtension P]
    [∀ P : (strictHenselizationScheme S
        (smallEtaleInverseImage_imagePoint g sbar') Rsh).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback c).op.HasLeftKanExtension P]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback g).op.HasLeftKanExtension P]
    [InitiallySmall
      ((smallEtalePullback g ⋙
        (GeometricPoint.toSmallEtalePoint sbar').fiber).Elements)]
    [InitiallySmall
      ((smallEtalePullback g ⋙
        (GeometricPoint.toSmallEtalePoint
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')).fiber).Elements)]
    [((smallEtalePullback g).sheafPushforwardContinuous (Type u)
        S.smallEtaleTopology S'.smallEtaleTopology).IsRightAdjoint]
    (hc'_over :
      c' ≫ strictHenselizationMap S' sbar' Rsh' =
        strictHenselizationMap S'
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') RshT')
    (hc_over :
      c ≫ strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar') Rsh =
        strictHenselizationMap S
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) RshT)
    (F : Sheaf S.smallEtaleTopology (Type u))
    (eS' :
      Scheme.Etale.stalk sbar'
          (((smallEtalePullback g).sheafPullback (Type u)
              S.smallEtaleTopology S'.smallEtaleTopology).obj F).obj ≃
        etaleGlobalSections
          (((smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (ePull' :
      (((smallEtalePullback c').sheafPullback (Type u)
          (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology
          (strictHenselizationScheme S'
            (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
            RshT').smallEtaleTopology).obj
          (((smallEtalePullback (strictHenselizationMap S' sbar' Rsh')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S' sbar' Rsh').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F))).obj.obj
        (op ((smallEtalePullback c').obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S' sbar' Rsh')) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (eT' :
      Scheme.Etale.stalk
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
          (((smallEtalePullback g).sheafPullback (Type u)
              S.smallEtaleTopology S'.smallEtaleTopology).obj F).obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT')).sheafPullback (Type u)
              S'.smallEtaleTopology
              (strictHenselizationScheme S'
                (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
                RshT').smallEtaleTopology).obj
            (((smallEtalePullback g).sheafPullback (Type u)
                S.smallEtaleTopology S'.smallEtaleTopology).obj F)))
    (eS :
      Scheme.Etale.stalk (smallEtaleInverseImage_imagePoint g sbar') F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
                Rsh)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology).obj F))
    (ePull :
      (((smallEtalePullback c).sheafPullback (Type u)
          (strictHenselizationScheme S
            (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology
          (strictHenselizationScheme S
            (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
            RshT).smallEtaleTopology).obj
          (((smallEtalePullback
              (strictHenselizationMap S (smallEtaleInverseImage_imagePoint g sbar')
                Rsh)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (smallEtaleInverseImage_imagePoint g sbar') Rsh).smallEtaleTopology).obj
            F)).obj.obj
        (op ((smallEtalePullback c).obj
          (MorphismProperty.Over.mk _
            (𝟙 (strictHenselizationScheme S
              (smallEtaleInverseImage_imagePoint g sbar') Rsh)) inferInstance))) ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT).smallEtaleTopology).obj F))
    (eT :
      Scheme.Etale.stalk
          (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h) F.obj ≃
        etaleGlobalSections
          (((smallEtalePullback
              (strictHenselizationMap S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT)).sheafPullback (Type u)
              S.smallEtaleTopology
              (strictHenselizationScheme S
                (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
                RshT).smallEtaleTopology).obj F))
    (x :
      (GeometricPoint.toSmallEtalePoint sbar').sheafFiber.obj
        (((smallEtalePullback g).sheafPullback (Type u)
            S.smallEtaleTopology S'.smallEtaleTopology).obj F)) :
    (étaleSpecializationMap_inverseImage_tbar_eq g sbar' Rsh' Rsh tbar' h hh ▸
        (smallEtaleInverseImage_stalkIso g
          (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar') F).hom)
      (étaleSpecializationMap S' sbar'
        (étaleSpecializationMap_inverseImage_tbarS' sbar' Rsh' tbar')
        Rsh' RshT' c' hc'_over
        (((smallEtalePullback g).sheafPullback (Type u)
            S.smallEtaleTopology S'.smallEtaleTopology).obj F)
        eS' ePull' eT' x) =
      étaleSpecializationMap S (smallEtaleInverseImage_imagePoint g sbar')
        (étaleSpecializationMap_inverseImage_tbar g sbar' Rsh' Rsh tbar' h)
        Rsh RshT c hc_over F eS ePull eT
        ((smallEtaleInverseImage_stalkIso g sbar' F).hom x) :=
  sorry

end AlgebraicGeometry.Scheme

end
