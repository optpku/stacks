/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Remark_63_10_9

/-!
# Vertical pasting of derived lower shriek and proper pushforward

Canonical Leray comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`, and the two pasted
paths of Lemma 63.8.1 comparisons along a vertically stacked pair of
commutative squares.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section PushforwardComp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (Λ : Type u) [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward f Λ).Additive]
variable [(etaleModulePushforward g Λ).Additive]
variable [(etaleModulePushforward (f ≫ g) Λ).Additive]
variable [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
  (HomologicalComplex.quasiIso
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Iterated cochain unit for `Rf_* ⋙ Rg_*` as a right-derived model of
`f_* ⋙ g_*`, using the two `RightDerived.Cochain.unit`s and the same
associator pattern as `etaleDerivedLowerShriekPushforward_leftUnit`. -/
def etaleDerivedPushforwardComp_iteratedUnit :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived X Λ) ⋙
        ((etaleDerivedPushforward f : EtaleDerived X Λ ⥤ EtaleDerived Y Λ) ⋙
          (etaleDerivedPushforward g : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)) :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
        (ComplexShape.up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Z Λ)).hom ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((etaleModulePushforward g Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Z Λ)).hom ≫
    whiskerLeft
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit (etaleModulePushforward g Λ)) ≫
    (Functor.associator
      ((etaleModulePushforward f Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Y Λ)
      (etaleDerivedPushforward g :
        EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)).inv ≫
    whiskerRight
      (RightDerived.Cochain.unit (etaleModulePushforward f Λ))
      (etaleDerivedPushforward g :
        EtaleDerived Y Λ ⥤ EtaleDerived Z Λ) ≫
    (Functor.associator
      (DerivedCategory.Q :
        CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived X Λ)
      (etaleDerivedPushforward f : EtaleDerived X Λ ⥤ EtaleDerived Y Λ)
      (etaleDerivedPushforward g : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ)).hom

/-- Derived identification of `R(f ≫ g)_*` with `R(g_* ∘ f_*)` along
`etaleModulePushforwardCompIso.symm`. -/
def etaleDerivedPushforwardComp_iso :
    RightDerived.Cochain.functor (etaleModulePushforward (f ≫ g) Λ) ≅
      RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (RightDerived.Cochain.unit (etaleModulePushforward (f ≫ g) Λ))
    (RightDerived.Cochain.unit
      (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCompIso f g).symm (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Z Λ))

/-- Canonical Leray comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`. -/
def etaleDerivedPushforwardComp :
    (etaleDerivedPushforward (f ≫ g) :
        EtaleDerived X Λ ⥤ EtaleDerived Z Λ) ⟶
      (etaleDerivedPushforward f : EtaleDerived X Λ ⥤ EtaleDerived Y Λ) ⋙
        (etaleDerivedPushforward g : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ) :=
  (etaleDerivedPushforwardComp_iso f g Λ).hom ≫
    (RightDerived.Cochain.functor
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ)).rightDerivedDesc
      (RightDerived.Cochain.unit
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
      ((etaleDerivedPushforward f : EtaleDerived X Λ ⥤ EtaleDerived Y Λ) ⋙
        (etaleDerivedPushforward g : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ))
      (etaleDerivedPushforwardComp_iteratedUnit f g Λ)

/-- Unfolding of `etaleDerivedPushforwardComp` as transport along the underived
composition isomorphism followed by the iterated-unit comparison. -/
theorem etaleDerivedPushforwardComp_eq :
    etaleDerivedPushforwardComp f g Λ =
      (etaleDerivedPushforwardComp_iso f g Λ).hom ≫
        (RightDerived.Cochain.functor
            (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ)).rightDerivedDesc
          (RightDerived.Cochain.unit
            (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
          (HomologicalComplex.quasiIso
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
          ((etaleDerivedPushforward f : EtaleDerived X Λ ⥤ EtaleDerived Y Λ) ⋙
            (etaleDerivedPushforward g : EtaleDerived Y Λ ⥤ EtaleDerived Z Λ))
          (etaleDerivedPushforwardComp_iteratedUnit f g Λ) :=
  sorry

/-- The derived pushforward comparison is an isomorphism, by K-injective
preservation for proper (flat) pushforward. -/
theorem etaleDerivedPushforwardComp_isIso :
    IsIso (etaleDerivedPushforwardComp f g Λ) :=
  sorry

end PushforwardComp

section VerticalComp

variable {X' X Y' Y Z' Z : Scheme.{u}}
variable (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y ⟶ Z) (g' : Y' ⟶ Z')
variable (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)
variable (h_top : CommSq k f' f l) (h_bot : CommSq l g' g m)
variable [IsProper f] [IsProper f'] [IsProper g] [IsProper g']
variable [IsSeparated k] [LocallyQuasiFinite k] [LocallyOfFiniteType k]
variable [IsSeparated l] [LocallyQuasiFinite l] [LocallyOfFiniteType l]
variable [IsSeparated m] [LocallyQuasiFinite m] [LocallyOfFiniteType m]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Whiskered composite of the two Lemma 63.8.1 square comparisons:
`m_! ∘ Rg'_* ∘ Rf'_* ⟶ Rg_* ∘ l_! ∘ Rf'_* ⟶ Rg_* ∘ Rf_* ∘ k_!`. -/
def etaleDerivedLowerShriekPushforward_vcomp_whisker
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙ etaleDerivedPushforward g' ⋙
        lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g :=
  whiskerLeft (etaleDerivedPushforward f')
      (etaleDerivedLowerShriekPushforward g g' m l h_bot Λ) ≫
    (Functor.associator (etaleDerivedPushforward f')
        (lowerShriekModuleDerived l Λ) (etaleDerivedPushforward g)).inv ≫
    whiskerRight (etaleDerivedLowerShriekPushforward f f' l k h_top Λ)
      (etaleDerivedPushforward g) ≫
    (Functor.associator (lowerShriekModuleDerived k Λ)
        (etaleDerivedPushforward f) (etaleDerivedPushforward g)).hom

/-- Inner pasted path: transport the whiskered square comparisons along
`R(f' ≫ g')_* ⟶ Rf'_* ⋙ Rg'_*`. -/
def etaleDerivedLowerShriekPushforward_vcomp_inner
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward (f' ≫ g') ⋙ lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g :=
  whiskerRight (etaleDerivedPushforwardComp f' g' Λ)
      (lowerShriekModuleDerived m Λ) ≫
    (Functor.associator (etaleDerivedPushforward f') (etaleDerivedPushforward g')
        (lowerShriekModuleDerived m Λ)).hom ≫
    etaleDerivedLowerShriekPushforward_vcomp_whisker f f' g g' k l m h_top h_bot Λ

/-- Outer pasted path: the Lemma 63.8.1 comparison of the outer rectangle,
transported along `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`. -/
def etaleDerivedLowerShriekPushforward_vcomp_outer
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f ≫ g) Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward (f' ≫ g') ⋙ lowerShriekModuleDerived m Λ ⟶
      lowerShriekModuleDerived k Λ ⋙ etaleDerivedPushforward f ⋙
        etaleDerivedPushforward g :=
  etaleDerivedLowerShriekPushforward (f ≫ g) (f' ≫ g') m k
      (h_top.vert_comp h_bot) Λ ≫
    whiskerLeft (lowerShriekModuleDerived k Λ)
      (etaleDerivedPushforwardComp f g Λ)

/-- Objectwise form of the vertical pasting identity. -/
theorem etaleDerivedLowerShriekPushforward_vcomp_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [(etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward (f ≫ g) Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ).Additive]
    [(etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ).Additive]
    [(etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ).Additive]
    [(etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ).Additive]
    [(lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward (f' ≫ g') Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ etaleModulePushforward g' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule l Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward g' Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule l Λ ⋙ etaleModulePushforward g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward (f' ≫ g') Λ ⋙ lowerShriekModule m Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule k Λ ⋙ etaleModulePushforward (f ≫ g) Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X' Λ) :
    (etaleDerivedLowerShriekPushforward_vcomp_inner f f' g g' k l m
        h_top h_bot Λ).app K =
      (etaleDerivedLowerShriekPushforward_vcomp_outer f f' g g' k l m
        h_top h_bot Λ).app K :=
  sorry

end VerticalComp

end AlgebraicGeometry.Scheme.Etale

end
