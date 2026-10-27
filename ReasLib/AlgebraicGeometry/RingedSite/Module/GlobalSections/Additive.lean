/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic

/-!
# Additivity of module global sections on ringed sites

This module records the additive structures needed to pass ordinary global-sections functors to
homotopy and derived categories.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z u v w

namespace RingedSite.Hom

/-- The additive global-sections functor on module sheaves is additive. -/
@[stacks 0D6H "additivity of module global sections", instance]
theorem moduleGlobalSectionsAdditiveFunctor_additive (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    (moduleGlobalSectionsAdditiveFunctor.{z} X).Additive := sorry

/-- The module-valued global-sections functor on a ringed site is additive. -/
@[instance] theorem moduleGlobalSectionsFunctor_additive (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] :
    (moduleGlobalSectionsFunctor.{z} X).Additive := sorry

end RingedSite.Hom
