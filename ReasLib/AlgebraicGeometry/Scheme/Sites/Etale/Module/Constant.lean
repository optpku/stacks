/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]

/-- Inverse image identifies a constant module sheaf with the same constant module sheaf. -/
def etaleConstantModulePullbackIso :
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) ≅
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ) :=
  let terminal := MorphismProperty.Over.mkIdTerminal (@Etale) Y
  let imageTerminal := IsTerminal.ofIso
    (MorphismProperty.Over.mkIdTerminal (@Etale) X)
    (Etale.globalEtalePullbackIso f).symm
  let sourceAdj := (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} Λ) terminal).comp
    ((smallEtalePullback f).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology)
  let targetAdj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} Λ) imageTerminal
  (sourceAdj.leftAdjointUniq targetAdj).app (ModuleCat.of Λ Λ)

/-- The canonical constant-module pullback morphism is the forward adjunction comparison. -/
def etaleConstantModulePullbackHom := (etaleConstantModulePullbackIso f Λ).hom

/-- The canonical pullback morphism of constant module sheaves is invertible. -/
instance isIso_etaleConstantModulePullbackHom :
    IsIso (etaleConstantModulePullbackHom f Λ) := by
  unfold etaleConstantModulePullbackHom
  infer_instance

variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Exact inverse image identifies the degree-zero constant module complexes. -/
def etaleConstantModuleDerivedPullbackIso :
    (etaleModuleDerivedInverseImage f Λ).obj
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ))) ≅
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) :=
  ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).mapDerivedCategorySingleFunctor (0 : ℤ)).app
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) ≪≫
  (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).mapIso
    (etaleConstantModulePullbackIso f Λ)

/-- The degree-zero constant comparison is induced by the sheaf comparison. -/
theorem etaleConstantModuleDerivedPullbackIso_hom :
    (etaleConstantModuleDerivedPullbackIso f Λ).hom =
    ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).mapDerivedCategorySingleFunctor (0 : ℤ)).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) ≫
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).map
      (etaleConstantModulePullbackIso f Λ).hom := rfl

end AlgebraicGeometry.Scheme.Etale

end
