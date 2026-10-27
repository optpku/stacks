/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Colimits of quasi-coherent modules
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty Opposite
  SheafOfModules SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- Quasi-coherent modules are closed under colimits in the ambient fppf
module category for every universe-compatible shape. -/
instance closedUnderColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J :=
  sorry

/-- The inclusion `QCoh 𝒪_X → Mod(𝒪_X)` creates colimits of every
universe-compatible shape. -/
instance inclusion_createsColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    CreatesColimitsOfShape J (quasiCoherentModuleProperty X).ι :=
  createsColimitsOfShapeFullSubcategoryInclusion J (quasiCoherentModuleProperty X)

/-- `QCoh 𝒪_X` has colimits of every universe-compatible shape. -/
instance hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (QCoh X) :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated Zariski module category. -/
instance toAssociatedModules_preservesColimitsOfShape_zariski
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .zariski) :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated étale module category. -/
instance toAssociatedModules_preservesColimitsOfShape_etale
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .etale) :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated fppf module category. -/
instance toAssociatedModules_preservesColimitsOfShape_fppf
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .fppf) :=
  sorry

/-- `toEtaleModules` preserves colimits of every universe-compatible shape. -/
instance toEtaleModules_preservesColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toEtaleModules X) :=
  sorry

/-- `toLQCoh` preserves colimits of every universe-compatible shape. -/
instance toLQCoh_preservesColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toLQCoh X) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
