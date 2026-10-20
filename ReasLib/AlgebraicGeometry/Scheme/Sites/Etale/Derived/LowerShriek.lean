/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u) [Ring Λ]
variable [LocallyOfFiniteType f] [IsSeparated f] [LocallyQuasiFinite f]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The functor on derived categories induced by exact proper-support direct image of module sheaves. -/
def etaleExactLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  (etaleModuleLowerShriek f Λ).mapDerivedCategory

/-- Exact derived proper-support direct image is induced by the module sheaf functor. -/
theorem etaleExactLowerShriek_def :
    etaleExactLowerShriek f Λ = (etaleModuleLowerShriek f Λ).mapDerivedCategory := rfl

end AlgebraicGeometry.Scheme.Etale

end
