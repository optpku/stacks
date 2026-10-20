/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.StandardSmall
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence

/-!
# Coefficient presentations on the small étale site

The canonical and standard structure sheaves are identified by identity maps on
global functions. Scalar restriction then identifies their module categories.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The canonical and standard étale structure sheaves are isomorphic by the
identity on the ring of global functions of each étale scheme. -/
def etaleStructureSheafIso (X : Scheme.{u}) :
    Etale.Small.structureSheaf X ≅ StandardSmall.structureSheaf .etale X where
  hom := ⟨{
    app U := RingCat.ofHom (RingHom.id _)
    naturality _ _ _ := by ext r; rfl }⟩
  inv := ⟨{
    app U := RingCat.ofHom (RingHom.id _)
    naturality _ _ _ := by ext r; rfl }⟩
  hom_inv_id := by ext U; rfl
  inv_hom_id := by ext U; rfl

/-- Scalar restriction along the identity on global functions identifies
canonical étale modules with the standard étale coefficient presentation. -/
def etaleModulePresentation (X : Scheme.{u}) :
    SheafOfModules.{u} (Etale.Small.structureSheaf X) ≌
      SheafOfModules.{u} (StandardSmall.structureSheaf .etale X) :=
  @SheafOfModules.CoefficientEquivalence.equivalence _ _ _ _ _ _
    (CategoryTheory.Equivalence.refl : X.Etale ≌ X.Etale)
    (by change (𝟭 X.Etale).IsContinuous X.smallEtaleTopology X.smallEtaleTopology
        infer_instance)
    (by change (𝟭 X.Etale).IsContinuous X.smallEtaleTopology X.smallEtaleTopology
        infer_instance) _ _
    (etaleStructureSheafIso X).symm

end AlgebraicGeometry.Scheme.AssociatedModule
