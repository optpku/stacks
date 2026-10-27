/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.DerivedAdjunction

/-!
# Unbounded derived module descent for terminal hypercoverings
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

variable {X : RingedSite.{u, v, w}}
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}] [UnivLE.{max u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- The canonical derived module unit of a terminal hypercovering is invertible at
every object of the unbounded derived category of module sheaves. -/
theorem derivedUnit_app_isIso [HasEqualizers X.carrier] [HasPullbacks X.carrier]
    (E : Hom.ModuleDerived.{w} X) :
    IsIso ((derivedUnit K).app E) := sorry

/-- The canonical derived module unit of a terminal hypercovering is an isomorphism
of functors on the unbounded derived category of module sheaves. -/
theorem derivedUnit_isIso [HasEqualizers X.carrier] [HasPullbacks X.carrier] :
    IsIso (derivedUnit K) := sorry

end RingedSite.Localization.AtSimplicialSR
