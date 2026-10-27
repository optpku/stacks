/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.DerivedSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Module-valued presheaves admit left Kan extensions along opposite small-étale
pullback for an étale morphism. -/
instance smallEtaleModulePullbackHasLeftKanExtension {A B : Scheme.{u}}
    (j : A ⟶ B) [Etale j] (Λ : Type u) [Ring Λ]
    (F : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (smallEtalePullback j).op.HasLeftKanExtension F := sorry

/-- The inverse-image square of module sheaves associated to a cartesian square
of schemes. -/
def etaleModuleSheafPullback_square {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback g).op.HasLeftKanExtension P]
    [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f').op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback g').op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P] :
    Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ) ≅
      Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ) :=
  Hom.etaleModuleSheafPullback_comp Λ g f' ≪≫
    Hom.etaleModuleSheafPullback_congr Λ h_cart.w.symm ≪≫
    (Hom.etaleModuleSheafPullback_comp Λ f g').symm

/-- Inverse image of module sheaves commutes with forgetting coefficients. -/
def etaleModuleSheafPullback_compSheafComposeIso {A B : Scheme.{u}}
    (h : A ⟶ B) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify A.smallEtaleTopology AddCommGrpCat.{u}]
    [A.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [B.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [A.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback h).op] :
    Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ) ⋙
        sheafCompose A.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose B.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianSheafPullback h :=
  Functor.sheafPullback.compSheafComposeIso (smallEtalePullback h)
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
    B.smallEtaleTopology A.smallEtaleTopology

/-- Derived inverse image `b⁻¹` on `D(X_étale, Λ)`, induced by the exact
small-étale inverse-image functor. -/
def etaleModuleDerivedInverseImage {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u)
    [Ring Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)).mapDerivedCategory

/-- Derived inverse image is `mapDerivedCategory` of module sheaf pullback. -/
theorem etaleModuleDerivedInverseImage_def {A B : Scheme.{u}} (h : A ⟶ B)
    (Λ : Type u) [Ring Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    etaleModuleDerivedInverseImage h Λ =
      (Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)).mapDerivedCategory :=
  sorry

/-- Evaluating derived inverse image on an object of `D(B_étale, Λ)`. -/
theorem etaleModuleDerivedInverseImage_obj {A B : Scheme.{u}} (h : A ⟶ B)
    (Λ : Type u) [Ring Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
    (K : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage h Λ).obj K =
      (Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)).mapDerivedCategory.obj K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
