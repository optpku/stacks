module

public import stacks_project.Chap59.Remark_59_75_8_Comparison
public import stacks_project.Chap59.Lemma_59_75_7
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section HenselInverseImage

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (s : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk s.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh]

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (henselizedFiberToX f s Rsh)).op.HasLeftKanExtension P]
variable [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]

/-- Derived inverse image of `K` along the henselized-fibre projection `p`. -/
noncomputable abbrev henselInverseImage
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory
      (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}) :=
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh)
      AddCommGrpCat.{u}).mapDerivedCategory.obj K

/-- Unfolding of `henselInverseImage` as derived inverse image along `p`. -/
theorem henselInverseImage_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    henselInverseImage f s Rsh K =
      (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh)
          AddCommGrpCat.{u}).mapDerivedCategory.obj K :=
  rfl

end HenselInverseImage

section FibreArrows

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (s : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk s.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh]
variable (i : Spec (.of s.K) ⟶ strictHenselizationScheme S s Rsh)
variable (hi : i ≫ strictHenselizationMap S s Rsh = s.hom)

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (pullback f s.hom).smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (pullback f s.hom).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (henselizedFiberToX f s Rsh)).op.HasLeftKanExtension P]
variable [∀ P : (henselizedFiber f s Rsh).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (geometricFiberToHenselized f s Rsh i hi)).op.HasLeftKanExtension P]
variable [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
    (geometricFiberToHenselized f s Rsh i hi) AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi) AddCommGrpCat.{u})]
variable [(ExactFunctor.of
    (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi)
      AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
variable [(siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor (pullback f s.hom).smallEtaleTopology
    ((smallEtalePullback (geometricFiberToHenselized f s Rsh i hi)).obj
      (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))).Additive]
variable [(Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi) AddCommGrpCat.{u} ⋙
    siteAbelianSectionsFunctor (pullback f s.hom).smallEtaleTopology
      ((smallEtalePullback (geometricFiberToHenselized f s Rsh i hi)).obj
        (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))).Additive]

/-- The Remark 59.53.2 restriction from henselized-fibre `RΓ` of `p⁻¹ K` to
geometric-fibre `RΓ`. -/
noncomputable abbrev henselToGeometricFibreCohomology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :=
  derivedEtaleSectionsPullback (geometricFiberToHenselized f s Rsh i hi)
    (henselInverseImage f s Rsh K)

/-- The Remark 59.53.2 geometric-fibre restriction is `RΓ`-pullback along
`geometricFiberToHenselized`. -/
theorem henselToGeometricFibreCohomology_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    henselToGeometricFibreCohomology f s Rsh i hi K =
      derivedEtaleSectionsPullback (geometricFiberToHenselized f s Rsh i hi)
        (henselInverseImage f s Rsh K) :=
  rfl

/-- Derived sections of the inverse image of `K` on the geometric fibre `X_s`. -/
noncomputable abbrev geometricFibreCohomology
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory AddCommGrpCat.{u} :=
  (siteAbelianSectionsDerived (pullback f s.hom).smallEtaleTopology
      ((smallEtalePullback (geometricFiberToHenselized f s Rsh i hi)).obj
        (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))).obj
    ((Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi)
        AddCommGrpCat.{u}).mapDerivedCategory.obj
      (henselInverseImage f s Rsh K))

/-- Unfolding of geometric-fibre `RΓ` after inverse image along
`geometricFiberToHenselized`. -/
theorem geometricFibreCohomology_eq
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    geometricFibreCohomology f s Rsh i hi K =
      (siteAbelianSectionsDerived (pullback f s.hom).smallEtaleTopology
          ((smallEtalePullback (geometricFiberToHenselized f s Rsh i hi)).obj
            (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))).obj
        ((Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f s Rsh i hi)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          (henselInverseImage f s Rsh K)) :=
  rfl

end FibreArrows

section IdentitySiteReassoc

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (sbar : GeometricPoint S)
variable (RshS : Type u) [CommRing RshS]
variable [Algebra (S.presheaf.stalk sbar.image) RshS]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar RshS))
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

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (henselizedFiberToX f sbar RshS)).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).op.HasLeftKanExtension P]
variable [∀ P : (henselizedFiber f sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).op.HasLeftKanExtension P]
variable [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)
      AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over) AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    (MorphismProperty.Over.mk _
      (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
      (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))).Additive]

/-- Identity-site reassociation of henselized-fibre `RΓ` after pullback along
`id_X × c`: the pulled identity object and `(id_X × c)⁻¹ (p_{s̄}⁻¹ K)` recover
identity-site `RΓ` of `p_{t̄}⁻¹ K`. -/
theorem idXTimesC_identitySiteReassoc
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (siteAbelianSectionsDerived
          (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
            (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))).obj
        ((Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          (henselInverseImage f sbar RshS K)) =
      (siteAbelianSectionsDerived
          (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))
            inferInstance)).obj
        (henselInverseImage f (imageGeometricPoint sbar RshS tbar) RshT K) := sorry

end IdentitySiteReassoc



section StalkToHensel

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (s : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk s.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh]

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (strictHenselizationScheme S s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (strictHenselizationScheme S s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [(etaleAbelianPushforward f).Additive]
variable [Functor.HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
  (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable [(etaleAbelianPushforward
    (pullback.snd f (strictHenselizationMap S s Rsh))).Additive]
variable [Functor.HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleAbelianPushforward (pullback.snd f (strictHenselizationMap S s Rsh))))
  (HomologicalComplex.quasiIso
    (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (strictHenselizationMap S s Rsh)).op.HasLeftKanExtension P]
variable [∀ P : (strictHenselizationScheme S s Rsh).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (pullback.snd f (strictHenselizationMap S s Rsh))).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (henselizedFiberToX f s Rsh)).op.HasLeftKanExtension P]
variable [(Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u})]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
    (pullback.snd f (strictHenselizationMap S s Rsh)) AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f (strictHenselizationMap S s Rsh)) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f (strictHenselizationMap S s Rsh)) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh) AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor
    (strictHenselizationScheme S s Rsh).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance)).Additive]

/-- The Remark 59.53.2 first horizontal
`(Rf_* K)_s ⟶ RΓ(X ×_S Spec(O^{sh}_{S,s}), p⁻¹ K)`, as the
`DerivedBaseChange.app` composite followed by identity-site comparison. -/
noncomputable def etaleStalkToHenselizedFibreCohomology
    (adjF :
      (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor (etaleAbelianPushforward f))
    (adjFsh :
      (Sheaf.smallEtaleInverseImage
          (pullback.snd f (strictHenselizationMap S s Rsh))
          AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor
          (etaleAbelianPushforward
            (pullback.snd f (strictHenselizationMap S s Rsh))))
    (square :
      (Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh)
            AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage
              (pullback.snd f (strictHenselizationMap S s Rsh))
              AddCommGrpCat.{u}).mapDerivedCategory ≅
        (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh)
              AddCommGrpCat.{u}).mapDerivedCategory)
    (sectionsFsh :
      RightDerived.Cochain.functor
            (etaleAbelianPushforward
              (pullback.snd f (strictHenselizationMap S s Rsh))) ⋙
          siteAbelianSectionsDerived
            (strictHenselizationScheme S s Rsh).smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh))
              inferInstance) ≅
        siteAbelianSectionsDerived (henselizedFiber f s Rsh).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (siteAbelianSectionsDerived
          (strictHenselizationScheme S s Rsh).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh))
            inferInstance)).obj
        ((Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh)
            AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K)) ⟶
      (siteAbelianSectionsDerived (henselizedFiber f s Rsh).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance)).obj
        (henselInverseImage f s Rsh K) :=
  (siteAbelianSectionsDerived
        (strictHenselizationScheme S s Rsh).smallEtaleTopology
        (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh))
          inferInstance)).map
      (DerivedBaseChange.app adjF adjFsh square K) ≫
    sectionsFsh.hom.app (henselInverseImage f s Rsh K)

/-- The first horizontal is the `DerivedBaseChange.app` composite of
Remark 59.53.2, followed by the identity-site comparison `sectionsFsh`. -/
theorem etaleStalkToHenselizedFibreCohomology_eq
    (adjF :
      (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor (etaleAbelianPushforward f))
    (adjFsh :
      (Sheaf.smallEtaleInverseImage
          (pullback.snd f (strictHenselizationMap S s Rsh))
          AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor
          (etaleAbelianPushforward
            (pullback.snd f (strictHenselizationMap S s Rsh))))
    (square :
      (Sheaf.smallEtaleInverseImage (strictHenselizationMap S s Rsh)
            AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage
              (pullback.snd f (strictHenselizationMap S s Rsh))
              AddCommGrpCat.{u}).mapDerivedCategory ≅
        (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage (henselizedFiberToX f s Rsh)
              AddCommGrpCat.{u}).mapDerivedCategory)
    (sectionsFsh :
      RightDerived.Cochain.functor
            (etaleAbelianPushforward
              (pullback.snd f (strictHenselizationMap S s Rsh))) ⋙
          siteAbelianSectionsDerived
            (strictHenselizationScheme S s Rsh).smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh))
              inferInstance) ≅
        siteAbelianSectionsDerived (henselizedFiber f s Rsh).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f s Rsh)) inferInstance))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    etaleStalkToHenselizedFibreCohomology f s Rsh adjF adjFsh square sectionsFsh K =
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S s Rsh).smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S s Rsh))
              inferInstance)).map
          (DerivedBaseChange.app adjF adjFsh square K) ≫
        sectionsFsh.hom.app (henselInverseImage f s Rsh K) :=
  rfl

end StalkToHensel

section LeftSquare

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (sbar : GeometricPoint S)
variable (RshS : Type u) [CommRing RshS]
variable [Algebra (S.presheaf.stalk sbar.image) RshS]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar RshS))
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

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (strictHenselizationScheme S sbar RshS).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [HasSheafify (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
  (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (strictHenselizationScheme S sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
  (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [(etaleAbelianPushforward f).Additive]
variable [Functor.HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
  (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable [(etaleAbelianPushforward
    (pullback.snd f (strictHenselizationMap S sbar RshS))).Additive]
variable [Functor.HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleAbelianPushforward (pullback.snd f (strictHenselizationMap S sbar RshS))))
  (HomologicalComplex.quasiIso
    (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [(etaleAbelianPushforward
    (pullback.snd f
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))).Additive]
variable [Functor.HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleAbelianPushforward
      (pullback.snd f
        (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))))
  (HomologicalComplex.quasiIso
    (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
      AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (strictHenselizationMap S sbar RshS)).op.HasLeftKanExtension P]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
      (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)).op.HasLeftKanExtension P]
variable [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback c).op.HasLeftKanExtension P]
variable [∀ P : (strictHenselizationScheme S sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (pullback.snd f (strictHenselizationMap S sbar RshS))).op.HasLeftKanExtension P]
variable [∀ P : (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).Etaleᵒᵖ ⥤
    AddCommGrpCat.{u},
  (smallEtalePullback
      (pullback.snd f
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (henselizedFiberToX f sbar RshS)).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).op.HasLeftKanExtension P]
variable [∀ P : (henselizedFiber f sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).op.HasLeftKanExtension P]

variable [(Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u})]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u})]
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
variable [(Sheaf.smallEtaleInverseImage
    (pullback.snd f (strictHenselizationMap S sbar RshS)) AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f (strictHenselizationMap S sbar RshS)) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f (strictHenselizationMap S sbar RshS)) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
      (pullback.snd f
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))
      AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))
      AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (pullback.snd f
          (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))
      AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS)
    AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
variable [(Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)
      AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits
  (Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
variable [PreservesFiniteColimits
  (Sheaf.smallEtaleInverseImage
      (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
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
    (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor
    (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    ((smallEtalePullback c).obj
      (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS)) inferInstance))).Additive]
variable [(Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u} ⋙
    siteAbelianSectionsFunctor
      (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
      ((smallEtalePullback c).obj
        (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
          inferInstance))).Additive]
variable [(siteAbelianSectionsFunctor
    (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    (MorphismProperty.Over.mk _
      (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
      inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor (henselizedFiber f sbar RshS).smallEtaleTopology
    (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance)).Additive]
variable [(siteAbelianSectionsFunctor
    (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
    (MorphismProperty.Over.mk _
      (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT)) inferInstance)).Additive]
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

/-- Remark 59.75.8 (1): for an arbitrary morphism `f : X ⟶ S` and
`K ∈ D(X_étale)`, the left square commutes in `D(Ab)`. The rows are the
Remark 59.53.2 first horizontals, instantiated as
`etaleStalkToHenselizedFibreCohomology` at `s̄` and at
the image of `t̄`, from the `RΓ(Spec(O^{sh}))` model of `(Rf_* K)_s` into
identity-site `RΓ` of `p⁻¹ K`. The left vertical is specialization
`derivedSpecializationMap` of `Rf_* K` along `c`. The middle vertical is
`derivedEtaleSectionsPullback` along `idXTimesC` of that `p⁻¹ K`, reassociated
onto identity-site `RΓ` by `idXTimesC_identitySiteReassoc`. There is no
quasi-compact, quasi-separated, or `D⁺` hypothesis. -/
@[stacks 0GJ9]
theorem derivedPushforward_specialization_leftSquare
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ePull :
      (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback c).obj
              (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
                inferInstance))).obj
          ((Sheaf.smallEtaleInverseImage c AddCommGrpCat.{u}).mapDerivedCategory.obj
            ((Sheaf.smallEtaleInverseImage (strictHenselizationMap S sbar RshS)
                AddCommGrpCat.{u}).mapDerivedCategory.obj
              ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K))) ≅
        (siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
              inferInstance)).obj
          ((Sheaf.smallEtaleInverseImage
              (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
              AddCommGrpCat.{u}).mapDerivedCategory.obj
            ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K)))
    (adjF :
      (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor (etaleAbelianPushforward f))
    (adjFshS :
      (Sheaf.smallEtaleInverseImage
          (pullback.snd f (strictHenselizationMap S sbar RshS))
          AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor
          (etaleAbelianPushforward
            (pullback.snd f (strictHenselizationMap S sbar RshS))))
    (adjFshT :
      (Sheaf.smallEtaleInverseImage
          (pullback.snd f
              (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))
          AddCommGrpCat.{u}).mapDerivedCategory ⊣
        RightDerived.Cochain.functor
          (etaleAbelianPushforward
            (pullback.snd f
                (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))))
    (squareS :
      (Sheaf.smallEtaleInverseImage (strictHenselizationMap S sbar RshS)
            AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage
              (pullback.snd f (strictHenselizationMap S sbar RshS))
              AddCommGrpCat.{u}).mapDerivedCategory ≅
        (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS)
              AddCommGrpCat.{u}).mapDerivedCategory)
    (squareT :
      (Sheaf.smallEtaleInverseImage
            (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
            AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage
              (pullback.snd f
                  (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))
              AddCommGrpCat.{u}).mapDerivedCategory ≅
        (Sheaf.smallEtaleInverseImage f AddCommGrpCat.{u}).mapDerivedCategory ⋙
          (Sheaf.smallEtaleInverseImage
              (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)
              AddCommGrpCat.{u}).mapDerivedCategory)
    (sectionsFshS :
      RightDerived.Cochain.functor
            (etaleAbelianPushforward
              (pullback.snd f (strictHenselizationMap S sbar RshS))) ⋙
          siteAbelianSectionsDerived
            (strictHenselizationScheme S sbar RshS).smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 (strictHenselizationScheme S sbar RshS))
              inferInstance) ≅
        siteAbelianSectionsDerived (henselizedFiber f sbar RshS).smallEtaleTopology
          (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))
    (sectionsFshT :
      RightDerived.Cochain.functor
            (etaleAbelianPushforward
              (pullback.snd f
                  (strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT))) ⋙
          siteAbelianSectionsDerived
            (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT))
              inferInstance) ≅
        siteAbelianSectionsDerived
            (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          (MorphismProperty.Over.mk _
            (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))
            inferInstance)) :
    CommSq
      (etaleStalkToHenselizedFibreCohomology f sbar RshS adjF adjFshS squareS sectionsFshS K)
      (derivedSpecializationMap S sbar (imageGeometricPoint sbar RshS tbar) RshS RshT c
        hc_over ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K) ePull)
      (derivedEtaleSectionsPullback (idXTimesC f sbar RshS tbar RshT c hc_over)
          (henselInverseImage f sbar RshS K) ≫
        eqToHom (idXTimesC_identitySiteReassoc f sbar RshS tbar RshT c hc_over K))
      (etaleStalkToHenselizedFibreCohomology f (imageGeometricPoint sbar RshS tbar) RshT
        adjF adjFshT squareT sectionsFshT K) := sorry

end LeftSquare

/-- Remark 59.75.8 (2): even when `f` is quasi-compact and quasi-separated and
`K` lies in `D⁺(X_étale)`, there is in general no morphism
`RΓ(X_{s̄}, K) ⟶ RΓ(X_{t̄}, K)` making the right square commute. The rows are
the Remark 59.53.2 maps `strictHenselizationToGeometricFiberCohomology`,
instantiated as `henselToGeometricFibreCohomology` at `s̄` and at the image of
`t̄`. The left vertical is `RΓ`-pullback along `idXTimesC` of `p⁻¹ K`,
reassociated by `idXTimesC_identitySiteReassoc`. -/
@[stacks 0GJ9]
theorem not_forall_exists_geometricFibreCohomologySpecialization :
    ¬ ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
        (sbar : GeometricPoint S) (RshS : Type u) [CommRing RshS]
        [Algebra (S.presheaf.stalk sbar.image) RshS]
        [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
        (tbar : GeometricPoint (strictHenselizationScheme S sbar RshS))
        (RshT : Type u) [CommRing RshT]
        [Algebra (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
        [IsStrictHenselizationOf
          (S.presheaf.stalk (imageGeometricPoint sbar RshS tbar).image) RshT]
        (c :
          strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT ⟶
            strictHenselizationScheme S sbar RshS)
        (hc_over :
          c ≫ strictHenselizationMap S sbar RshS =
            strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT)
        (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
        (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom)
        (iT :
          Spec (.of (imageGeometricPoint sbar RshS tbar).K) ⟶
            strictHenselizationScheme S (imageGeometricPoint sbar RshS tbar) RshT)
        (hiT :
          iT ≫ strictHenselizationMap S (imageGeometricPoint sbar RshS tbar) RshT =
            (imageGeometricPoint sbar RshS tbar).hom)
        [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify
          (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
          AddCommGrpCat.{u}]
        [HasSheafify (pullback f sbar.hom).smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify
          (pullback f (imageGeometricPoint sbar RshS tbar).hom).smallEtaleTopology
          AddCommGrpCat.{u}]
        [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
        [IsGrothendieckAbelian
          (Sheaf (henselizedFiber f sbar RshS).smallEtaleTopology AddCommGrpCat.{u})]
        [IsGrothendieckAbelian
          (Sheaf (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            AddCommGrpCat.{u})]
        [IsGrothendieckAbelian
          (Sheaf (pullback f sbar.hom).smallEtaleTopology AddCommGrpCat.{u})]
        [IsGrothendieckAbelian
          (Sheaf (pullback f (imageGeometricPoint sbar RshS tbar).hom).smallEtaleTopology
            AddCommGrpCat.{u})]
        [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (smallEtalePullback (henselizedFiberToX f sbar RshS)).op.HasLeftKanExtension P]
        [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (smallEtalePullback
              (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)).op.HasLeftKanExtension P]
        [∀ P : (henselizedFiber f sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (smallEtalePullback (geometricFiberToHenselized f sbar RshS iS hiS)).op.HasLeftKanExtension P]
        [∀ P : (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).Etaleᵒᵖ ⥤
            AddCommGrpCat.{u},
          (smallEtalePullback
              (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)).op.HasLeftKanExtension P]
        [∀ P : (henselizedFiber f sbar RshS).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).op.HasLeftKanExtension P]
        [(Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u}).Additive]
        [PreservesFiniteLimits
          (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
        [PreservesFiniteColimits
          (Sheaf.smallEtaleInverseImage (henselizedFiberToX f sbar RshS) AddCommGrpCat.{u})]
        [(Sheaf.smallEtaleInverseImage
            (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT)
            AddCommGrpCat.{u}).Additive]
        [PreservesFiniteLimits
          (Sheaf.smallEtaleInverseImage
              (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
        [PreservesFiniteColimits
          (Sheaf.smallEtaleInverseImage
              (henselizedFiberToX f (imageGeometricPoint sbar RshS tbar) RshT) AddCommGrpCat.{u})]
        [(Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f sbar RshS iS hiS)
            AddCommGrpCat.{u}).Additive]
        [PreservesFiniteLimits
          (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f sbar RshS iS hiS)
            AddCommGrpCat.{u})]
        [PreservesFiniteColimits
          (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f sbar RshS iS hiS)
            AddCommGrpCat.{u})]
        [(ExactFunctor.of
            (Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f sbar RshS iS hiS)
              AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
        [(Sheaf.smallEtaleInverseImage
            (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)
            AddCommGrpCat.{u}).Additive]
        [PreservesFiniteLimits
          (Sheaf.smallEtaleInverseImage
              (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)
              AddCommGrpCat.{u})]
        [PreservesFiniteColimits
          (Sheaf.smallEtaleInverseImage
              (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)
              AddCommGrpCat.{u})]
        [(ExactFunctor.of
            (Sheaf.smallEtaleInverseImage
                (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)
                AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
        [(Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
            AddCommGrpCat.{u}).Additive]
        [PreservesFiniteLimits
          (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
            AddCommGrpCat.{u})]
        [PreservesFiniteColimits
          (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
            AddCommGrpCat.{u})]
        [(ExactFunctor.of
            (Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
              AddCommGrpCat.{u})).obj.PreservesInjectiveObjects]
        [(siteAbelianSectionsFunctor (henselizedFiber f sbar RshS).smallEtaleTopology
            (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance)).Additive]
        [(siteAbelianSectionsFunctor
            (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            (MorphismProperty.Over.mk _
              (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT)) inferInstance)).Additive]
        [(siteAbelianSectionsFunctor (pullback f sbar.hom).smallEtaleTopology
            ((smallEtalePullback (geometricFiberToHenselized f sbar RshS iS hiS)).obj
              (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))).Additive]
        [(Sheaf.smallEtaleInverseImage (geometricFiberToHenselized f sbar RshS iS hiS)
              AddCommGrpCat.{u} ⋙
            siteAbelianSectionsFunctor (pullback f sbar.hom).smallEtaleTopology
              ((smallEtalePullback (geometricFiberToHenselized f sbar RshS iS hiS)).obj
                (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
                  inferInstance))).Additive]
        [(siteAbelianSectionsFunctor
            (pullback f (imageGeometricPoint sbar RshS tbar).hom).smallEtaleTopology
            ((smallEtalePullback
                (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)).obj
              (MorphismProperty.Over.mk _
                (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))
                inferInstance))).Additive]
        [(Sheaf.smallEtaleInverseImage
              (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)
              AddCommGrpCat.{u} ⋙
            siteAbelianSectionsFunctor
              (pullback f (imageGeometricPoint sbar RshS tbar).hom).smallEtaleTopology
              ((smallEtalePullback
                  (geometricFiberToHenselized f (imageGeometricPoint sbar RshS tbar) RshT iT hiT)).obj
                (MorphismProperty.Over.mk _
                  (𝟙 (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT))
                  inferInstance))).Additive]
        [(siteAbelianSectionsFunctor
            (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
            ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
              (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS)) inferInstance))).Additive]
        [(Sheaf.smallEtaleInverseImage (idXTimesC f sbar RshS tbar RshT c hc_over)
              AddCommGrpCat.{u} ⋙
            siteAbelianSectionsFunctor
              (henselizedFiber f (imageGeometricPoint sbar RshS tbar) RshT).smallEtaleTopology
              ((smallEtalePullback (idXTimesC f sbar RshS tbar RshT c hc_over)).obj
                (MorphismProperty.Over.mk _ (𝟙 (henselizedFiber f sbar RshS))
                  inferInstance))).Additive]
        (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
      ∃ (φ :
          geometricFibreCohomology f sbar RshS iS hiS (DerivedCategory.Plus.ι.obj K) ⟶
            geometricFibreCohomology f (imageGeometricPoint sbar RshS tbar) RshT iT hiT
              (DerivedCategory.Plus.ι.obj K)),
        CommSq
          (henselToGeometricFibreCohomology f sbar RshS iS hiS (DerivedCategory.Plus.ι.obj K))
          (derivedEtaleSectionsPullback (idXTimesC f sbar RshS tbar RshT c hc_over)
              (henselInverseImage f sbar RshS (DerivedCategory.Plus.ι.obj K)) ≫
            eqToHom
              (idXTimesC_identitySiteReassoc f sbar RshS tbar RshT c hc_over
                (DerivedCategory.Plus.ι.obj K)))
          φ
          (henselToGeometricFibreCohomology f (imageGeometricPoint sbar RshS tbar) RshT iT hiT
            (DerivedCategory.Plus.ι.obj K)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
