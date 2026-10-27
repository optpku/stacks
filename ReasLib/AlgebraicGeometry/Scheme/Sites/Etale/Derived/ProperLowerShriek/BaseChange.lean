/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' X₁ Y₁ X'₁ Y'₁ : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (Λ : Type u) [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'₁.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y'₁.smallEtaleTopology (ModuleCat.{u} Λ)]
variable (b : Y₁ ⟶ Y) (b' : Y'₁ ⟶ Y') (a : X₁ ⟶ X) (a' : X'₁ ⟶ X')
variable (f₁ : X₁ ⟶ Y₁) (f'₁ : X'₁ ⟶ Y'₁) (g₁ : Y'₁ ⟶ Y₁) (g'₁ : X'₁ ⟶ X₁)
variable (h_sq : CommSq g' f' f g) (h_sq₁ : CommSq g'₁ f'₁ f₁ g₁)
variable (h_Y' : IsPullback b' g₁ g b) (h_X : IsPullback a f₁ f b)
variable (h_X' : IsPullback a' f'₁ f' b') (h_back : IsPullback a' g'₁ g' a)
variable [IsProper f] [IsProper f']
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [IsSeparated g'] [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'₁.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X₁.Etale,
  HasWeakSheafify (X₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y₁.Etale,
  HasWeakSheafify (Y₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : X'₁.Etale,
  HasWeakSheafify (X'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'₁.Etale,
  HasWeakSheafify (Y'₁.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'₁.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f₁).op.HasLeftKanExtension P]
variable [∀ P : Y'₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f'₁).op.HasLeftKanExtension P]
variable [∀ P : Y₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g₁).op.HasLeftKanExtension P]
variable [∀ P : X₁.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g'₁).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f₁ ≫ b)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f'₁ ≫ b')).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ f')).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g'₁ ≫ a)).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (a' ≫ g')).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension P]
variable [∀ P : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a').op]

/-- Left vertical of the `2×3` diagram: the proper-pushforward/compact-support comparison of the
original square, whiskered by inverse image along `b`. -/
def etaleDerivedLowerShriekPushforward_baseChange_leftVertical
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f' ⋙
        lowerShriekModuleDerived g Λ ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      lowerShriekModuleDerived g' Λ ⋙
        etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage b Λ :=
  (Functor.associator (etaleDerivedPushforward f') (lowerShriekModuleDerived g Λ)
      (etaleModuleDerivedInverseImage b Λ)).inv ≫
    whiskerRight
      (etaleDerivedLowerShriekPushforward f f' g g' h_sq Λ)
      (etaleModuleDerivedInverseImage b Λ) ≫
    (Functor.associator (lowerShriekModuleDerived g' Λ) (etaleDerivedPushforward f)
      (etaleModuleDerivedInverseImage b Λ)).hom

/-- Evaluating the left vertical at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_leftVertical_app
    [(etaleModulePushforward f Λ).Additive]
    [(etaleModulePushforward f' Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage b Λ).obj
      ((lowerShriekModuleDerived g Λ).obj
        ((etaleDerivedPushforward f').obj K)) ⟶
      (etaleModuleDerivedInverseImage b Λ).obj
        ((etaleDerivedPushforward f).obj
          ((lowerShriekModuleDerived g' Λ).obj K)) :=
  (etaleDerivedLowerShriekPushforward_baseChange_leftVertical
      f g f' g' Λ b h_sq).app K

/-- Right vertical of the `2×3` diagram: inverse image along `a'` followed by
the proper-pushforward/compact-support comparison of the base-changed square. -/
def etaleDerivedLowerShriekPushforward_baseChange_rightVertical :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
    letI : IsProper f₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
    letI : IsProper f'₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f₁ Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))],
    etaleModuleDerivedInverseImage a' Λ ⋙
        etaleDerivedPushforward f'₁ ⋙ lowerShriekModuleDerived g₁ Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        lowerShriekModuleDerived g'₁ Λ ⋙ etaleDerivedPushforward f₁  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
  letI : IsProper f₁ :=
    MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
  letI : IsProper f'₁ :=
    MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
  letI : IsSeparated g₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
  letI : LocallyQuasiFinite g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
  letI : LocallyOfFiniteType g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
  letI : IsSeparated g'₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
  letI : LocallyQuasiFinite g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
  letI : LocallyOfFiniteType g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
  whiskerLeft
    (etaleModuleDerivedInverseImage a' Λ)
    (etaleDerivedLowerShriekPushforward f₁ f'₁ g₁ g'₁ h_sq₁ Λ)

/-- Evaluating the right vertical at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_rightVertical_app :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
    letI : IsProper f₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
    letI : IsProper f'₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f₁ Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))),
    (lowerShriekModuleDerived g₁ Λ).obj
      ((etaleDerivedPushforward f'₁).obj
        ((etaleModuleDerivedInverseImage a' Λ).obj K)) ⟶
      (etaleDerivedPushforward f₁).obj
        ((lowerShriekModuleDerived g'₁ Λ).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K))  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
  letI : IsProper f₁ :=
    MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
  letI : IsProper f'₁ :=
    MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
  letI : IsSeparated g₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
  letI : LocallyQuasiFinite g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
  letI : LocallyOfFiniteType g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
  letI : IsSeparated g'₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
  letI : LocallyQuasiFinite g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
  letI : LocallyOfFiniteType g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
  fun (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ↦
    (etaleDerivedLowerShriekPushforward_baseChange_rightVertical
        f g f' g' Λ b b' a a' f₁ f'₁ g₁ g'₁ h_sq₁ h_Y' h_X h_X' h_back).app K

/-- Top horizontal of the `2×3` diagram: compact-support base change of `g`
along `h_Y'`, then `Rf'_*` base change along `h_X'`. -/
def etaleDerivedLowerShriekPushforward_baseChange_top :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    ∀ [(etaleModulePushforward f' Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))],
    etaleDerivedPushforward f' ⋙
        lowerShriekModuleDerived g Λ ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        etaleDerivedPushforward f'₁ ⋙ lowerShriekModuleDerived g₁ Λ  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
  letI : IsSeparated g₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
  letI : LocallyQuasiFinite g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
  letI : LocallyOfFiniteType g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
  whiskerLeft (etaleDerivedPushforward f')
      (lowerShriekModuleDerivedBaseChange g b g₁ b' h_Y' Λ) ≫
    (Functor.associator (etaleDerivedPushforward f') (etaleModuleDerivedInverseImage b' Λ)
      (lowerShriekModuleDerived g₁ Λ)).inv ≫
    whiskerRight
      (etaleDerivedPushforwardBaseChange f' b' f'₁ a' h_X' Λ)
      (lowerShriekModuleDerived g₁ Λ) ≫
    (Functor.associator (etaleModuleDerivedInverseImage a' Λ) (etaleDerivedPushforward f'₁)
      (lowerShriekModuleDerived g₁ Λ)).hom

/-- Evaluating the top horizontal at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_top_app :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    ∀ [(etaleModulePushforward f' Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))),
    (etaleModuleDerivedInverseImage b Λ).obj
      ((lowerShriekModuleDerived g Λ).obj
        ((etaleDerivedPushforward f').obj K)) ⟶
      (lowerShriekModuleDerived g₁ Λ).obj
        ((etaleDerivedPushforward f'₁).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K))  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
  letI : IsSeparated g₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
  letI : LocallyQuasiFinite g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
  letI : LocallyOfFiniteType g₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
  fun (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ↦
    (etaleDerivedLowerShriekPushforward_baseChange_top
        g f' Λ b b' a' f'₁ g₁ h_Y' h_X').app K

/-- Bottom horizontal of the `2×3` diagram: `Rf_*` base change along `h_X`,
then compact-support base change of `g'` along `h_back`. -/
def etaleDerivedLowerShriekPushforward_baseChange_bottom :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f Λ).Additive]
      [(etaleModulePushforward f₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))],
    lowerShriekModuleDerived g' Λ ⋙
        etaleDerivedPushforward f ⋙ etaleModuleDerivedInverseImage b Λ ⟶
      etaleModuleDerivedInverseImage a' Λ ⋙
        lowerShriekModuleDerived g'₁ Λ ⋙ etaleDerivedPushforward f₁  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
  letI : IsSeparated g'₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
  letI : LocallyQuasiFinite g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
  letI : LocallyOfFiniteType g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
  whiskerLeft (lowerShriekModuleDerived g' Λ)
      (etaleDerivedPushforwardBaseChange f b f₁ a h_X Λ) ≫
    (Functor.associator (lowerShriekModuleDerived g' Λ) (etaleModuleDerivedInverseImage a Λ)
      (etaleDerivedPushforward f₁)).inv ≫
    whiskerRight
      (lowerShriekModuleDerivedBaseChange g' a g'₁ a' h_back Λ)
      (etaleDerivedPushforward f₁) ≫
    (Functor.associator (etaleModuleDerivedInverseImage a' Λ) (lowerShriekModuleDerived g'₁ Λ)
      (etaleDerivedPushforward f₁)).hom

/-- Evaluating the bottom horizontal at an object of `D(X'_étale, Λ)`. -/
def etaleDerivedLowerShriekPushforward_baseChange_bottom_app :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f Λ).Additive]
      [(etaleModulePushforward f₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))),
    (etaleModuleDerivedInverseImage b Λ).obj
      ((etaleDerivedPushforward f).obj
        ((lowerShriekModuleDerived g' Λ).obj K)) ⟶
      (etaleDerivedPushforward f₁).obj
        ((lowerShriekModuleDerived g'₁ Λ).obj
          ((etaleModuleDerivedInverseImage a' Λ).obj K))  :=
  -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
  letI : IsSeparated g'₁ :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
  letI : LocallyQuasiFinite g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
  -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
  letI : LocallyOfFiniteType g'₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
  fun (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ↦
    (etaleDerivedLowerShriekPushforward_baseChange_bottom
        f g' Λ b a a' f₁ g'₁ h_X h_back).app K

/-- Functor-level commutativity of the outer `2×3` rectangle. -/
theorem etaleDerivedLowerShriekPushforward_baseChange_natTrans :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
    letI : IsProper f₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
    letI : IsProper f'₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f Λ).Additive]
      [(etaleModulePushforward f' Λ).Additive]
      [(etaleModulePushforward f₁ Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))],
    etaleDerivedLowerShriekPushforward_baseChange_top
        g f' Λ b b' a' f'₁ g₁ h_Y' h_X' ≫
      etaleDerivedLowerShriekPushforward_baseChange_rightVertical
        f g f' g' Λ b b' a a' f₁ f'₁ g₁ g'₁ h_sq₁ h_Y' h_X h_X' h_back =
      etaleDerivedLowerShriekPushforward_baseChange_leftVertical
          f g f' g' Λ b h_sq ≫
        etaleDerivedLowerShriekPushforward_baseChange_bottom
          f g' Λ b a a' f₁ g'₁ h_X h_back  := sorry

/-- Proper pushforward and compact-support comparison commutes with arbitrary base change on unbounded derived étale module sheaves. -/
theorem etaleDerivedLowerShriekPushforward_baseChange :
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f₁ from the original morphism.
    letI : IsProper f₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsProper f'₁ from the original morphism.
    letI : IsProper f'₁ :=
      MorphismProperty.of_isPullback (P := @IsProper) h_X' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g₁ from the original morphism.
    letI : IsSeparated g₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g₁ from the original morphism.
    letI : LocallyQuasiFinite g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g₁ from the original morphism.
    letI : LocallyOfFiniteType g₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_Y' inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives IsSeparated g'₁ from the original morphism.
    letI : IsSeparated g'₁ :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyQuasiFinite g'₁ from the original morphism.
    letI : LocallyQuasiFinite g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h_back inferInstance
    -- Local instance justification (proof-local temporary data): the cartesian face derives LocallyOfFiniteType g'₁ from the original morphism.
    letI : LocallyOfFiniteType g'₁ :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_back inferInstance
    ∀ [(etaleModulePushforward f Λ).Additive]
      [(etaleModulePushforward f' Λ).Additive]
      [(etaleModulePushforward f₁ Λ).Additive]
      [(etaleModulePushforward f'₁ Λ).Additive]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f' Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward f'₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f' Λ ⋙ lowerShriekModule g Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g' Λ ⋙ etaleModulePushforward f Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (etaleModulePushforward f'₁ Λ ⋙ lowerShriekModule g₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule g'₁ Λ ⋙ etaleModulePushforward f₁ Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X'₁.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
      (K : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))),
    CommSq
      ((etaleDerivedLowerShriekPushforward_baseChange_top
          g f' Λ b b' a' f'₁ g₁ h_Y' h_X').app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_leftVertical
          f g f' g' Λ b h_sq).app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_rightVertical
        f g f' g' Λ b b' a a' f₁ f'₁ g₁ g'₁ h_sq₁ h_Y' h_X h_X' h_back).app K)
      ((etaleDerivedLowerShriekPushforward_baseChange_bottom
          f g' Λ b a a' f₁ g'₁ h_X h_back).app K)  := sorry

end AlgebraicGeometry.Scheme.Etale

end
