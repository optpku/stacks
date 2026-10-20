/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.OfModule
import StacksCheckRecall

/-!
# Canonical formal gluing

The source's formal-gluing category, canonical functor, and degree-zero functor are recalled from
their reusable ReasLib owners.

@stack 05EL
-/

@[expose] public section

/- Remark 15.90.10 (1) (Stacks 05EL): a ring map and principal-open family determine the
formal-gluing category. -/
@[stacks 05EL "Remark 15.90.10 (1)"] #check
  @LocalizedModule.Away.FormalGluing

@[stacks 05EL "Remark 15.90.10 (1), morphisms"]
#check @LocalizedModule.Away.FormalGluing.Hom

@[stacks 05EL "Remark 15.90.10 (1), category structure"]
#check @LocalizedModule.Away.FormalGluing.instCategory

/- Remark 15.90.10 (2): the canonical functor from `R`-modules to formal-gluing data. -/
@[stacks 05EL "Remark 15.90.10 (2)"]
#check @LocalizedModule.Away.FormalGluing.ofModuleFunctor

/- Remark 15.90.10 (3): the degree-zero functor from formal-gluing data to `R`-modules. -/
@[stacks 05EL "Remark 15.90.10 (3)"]
#check @LocalizedModule.Away.FormalGluing.h0Functor
