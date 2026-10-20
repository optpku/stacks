/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.20.7 core API

The reusable owners for sections after forgetting scalars live in
`ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying`.
This compatibility file only recalls that public interface.
-/

/- Lemma 21.20.7 (0D6J) recalls the reusable objectwise sections models. -/
@[stacks 0D6J "supporting objectwise model"]
#check @RingedSite.Hom.ModuleSections.sectionForget
#check @RingedSite.Hom.ModuleSections.Underlying.sections
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsToDerived
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsDerived
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsForgetIso
#check @RingedSite.Hom.ModuleSections.Underlying.sectionsCompIso
