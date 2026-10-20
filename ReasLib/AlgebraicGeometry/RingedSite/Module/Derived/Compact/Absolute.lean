/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.LocalizedGenerator
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Dimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute compactness of localized generators

Finite cohomological dimension upgrades the relative compactness of a localized generator to
ordinary compactness.  The hypotheses are expressed through the reusable right-derived sections
predicates, rather than through a presentation-specific expansion of cohomology groups.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived.LocalizedGenerator

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]

/-- Lemma 21.52.5 (094D): finite cohomological dimension and coproduct compatibility of module
sections over `U` make the degree-zero localized generator an ordinary compact object. -/
@[stacks 094D]
theorem isCompactObject_of_finiteDimension (U : X)
    [(SheafOfModules.Localization.restriction X.structureSheaf U :
      RingedSite.ModuleCat.{w} X ⥤
        SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint]
    (hfinite : ModuleCohomology.HasFiniteDimension X U)
    (hcoproduct : ModuleCohomology.PreservesCoproducts X U) :
    IsCompactObject (localizedGenerator X U) := sorry

end RingedSite.Hom.ModuleDerived.LocalizedGenerator

end
