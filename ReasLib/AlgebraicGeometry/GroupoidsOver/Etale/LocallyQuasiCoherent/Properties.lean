/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Closure properties of locally quasi-coherent étale modules

Locally quasi-coherent modules form a colimit-closed weak Serre subcategory of
étale modules. They are closed under tensor products and internal Hom from
finitely presented locally quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
open AlgebraicGeometry
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCoh

/-- Locally quasi-coherent étale modules are closed under colimits of arbitrary shape. -/
@[stacks 06WM]
instance closedUnderColimitsOfShape (X : GroupoidsOver S)
    (J : Type v) [Category.{w} J] :
    (locallyQuasiCoherent X).IsClosedUnderColimitsOfShape J := sorry

/-- Locally quasi-coherent étale modules form a weak Serre class in the ambient module category. -/
@[stacks 06WM]
instance isWeakSerreClass (X : GroupoidsOver S) :
    (locallyQuasiCoherent X).IsWeakSerreClass := sorry

end LQCoh

/-- In a short exact sequence of étale modules, local quasi-coherence of two terms implies local quasi-coherence of all three. -/
@[stacks 06WM]
theorem isLocallyQuasiCoherent_of_shortExact_two_out_of_three
    {X : GroupoidsOver S} {sc : ShortComplex (etaleModules X)} (hsc : sc.ShortExact)
    (h : (locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂) ∨
        (locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₃) ∨
        (locallyQuasiCoherent X sc.X₂ ∧ locallyQuasiCoherent X sc.X₃)) :
    locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂ ∧
      locallyQuasiCoherent X sc.X₃ := sorry

/-- The ambient tensor product of two locally quasi-coherent étale modules is locally quasi-coherent. -/
@[stacks 06WM]
instance isLocallyQuasiCoherent_tensor {X : GroupoidsOver S}
    (F G : etaleModules X) [IsLocallyQuasiCoherent F] [IsLocallyQuasiCoherent G] :
    IsLocallyQuasiCoherent (moduleTensorEtale F G) := sorry

/-- The internal Hom from a finitely presented locally quasi-coherent étale module to a locally quasi-coherent étale module is locally quasi-coherent. -/
@[stacks 06WM]
instance isLocallyQuasiCoherent_internalHom {X : GroupoidsOver S}
    (F G : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      X.etaleTopology (commEtaleStructureSheafLift X))
    [F.IsFinitePresentation] [IsLocallyQuasiCoherentLift F]
    [IsLocallyQuasiCoherentLift G] :
    IsLocallyQuasiCoherentLift ((ihom F).obj G) := sorry

end AlgebraicGeometry.GroupoidsOver
