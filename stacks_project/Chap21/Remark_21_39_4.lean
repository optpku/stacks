/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Sections
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Remark 21.39.4 (08Q6): evaluation of a complex of presheaves at `U` maps canonically to its
derived colimit, both for abelian groups and for modules over a ring `B`. The reusable
coefficient-general owner is `CategoryTheory.DerivedColimit`. -/

@[stacks 08Q6 "coefficient-general section complex to derived colimit"]
#check @CategoryTheory.DerivedColimit.sectionComplexToDerivedColimit

@[stacks 08Q6 "abelian section complex to derived colimit"]
#check @CategoryTheory.DerivedColimit.sectionComplexToLeftDerivedColimit

@[stacks 08Q6 "module section complex to derived colimit"]
#check @CategoryTheory.DerivedColimit.moduleSectionComplexToLeftDerivedColimit
