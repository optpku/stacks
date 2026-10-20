/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Hom
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.9.7 (Tag 07K0): the Hom-form universal property of module localization.

@stack 07K0
-/

@[stacks 07K0 "generic localized-module Hom equivalence"]
#check @IsLocalizedModule.homLinearEquiv

@[stacks 07K0 "generic localized-module Hom equivalence inverse"]
#check @IsLocalizedModule.homLinearEquiv_symm_apply

@[stacks 07K0 "canonical localized-module Hom equivalence"]
#check @LocalizedModule.homLinearEquiv

@[stacks 07K0 "source precomposition formula"]
#check @LocalizedModule.homLinearEquiv_apply

@[stacks 07K0 "canonical universal lift formula"]
#check @LocalizedModule.homLinearEquiv_symm_apply
