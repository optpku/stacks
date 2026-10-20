/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.5

The reusable owners for this item live in `ReasLib`.  The first clause is the module-valued
derived global-sections/direct-image comparison.  The second clause is its specialization at an
object `V : Y`, with restriction of scalars along
`sectionsRingMap f V : Γ(V, 𝒪_Y) →+* Γ(f(V), 𝒪_X)`.  This chapter file is deliberately a recall
surface: it introduces no chapter-local functors, instances, notation, or comparison wrappers.
-/

/- Lemma 21.20.5 (0D6H): for a morphism of ringed sites `f : X ⟶ Y`, the canonical map
`RΓ(X, -) ⟶ Rf_* ⋙ RΓ(Y, -)` is an isomorphism; for every `V : Y`, the corresponding map
`RΓ(f(V), -) ⋙ Res_{Γ(V,𝒪_Y)}^{Γ(f(V),𝒪_X)} ⟶ Rf_* ⋙ RΓ(V, -)` is an isomorphism. -/
@[stacks 0D6H "derived global-sections comparison"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison

@[stacks 0D6H "derived global-sections comparison isomorphism"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison_isIso

@[stacks 0D6H "derived global-sections comparison component"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison_app_isIso

@[stacks 0D6H "derived global-sections comparison isomorphism"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardIso

/- Objectwise API for the second clause. -/
@[stacks 0D6H "section-ring map"]
#check @RingedSite.Hom.sectionsRingMap

@[stacks 0D6H "section-ring restriction"]
#check @RingedSite.Hom.sectionsRestriction

@[stacks 0D6H "derived section-ring restriction"]
#check @RingedSite.Hom.sectionsRestrictionDerived

@[stacks 0D6H "objectwise sections comparison"]
#check @RingedSite.Hom.ModuleSections.objectPushforwardComparison

@[stacks 0D6H "objectwise sections comparison isomorphism"]
#check @RingedSite.Hom.ModuleSections.objectPushforwardComparison_isIso

@[stacks 0D6H "objectwise sections comparison component"]
#check @RingedSite.Hom.ModuleSections.objectPushforwardComparison_app_isIso

@[stacks 0D6H "objectwise sections comparison isomorphism"]
#check @RingedSite.Hom.ModuleSections.objectPushforwardIso
