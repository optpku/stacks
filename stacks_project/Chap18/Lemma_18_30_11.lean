/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
import StacksCheckRecall

@[expose] public section

/- The reusable generator-kernel hypothesis asks only about maps between finite coproducts of
selected generators. -/
@[stacks 093H "generator-kernel condition"]
#check @CategoryTheory.Functor.FiniteCokernelPresentation.HasKernels

/- Lemma 18.30.11: under the generator-kernel condition, finite basis presentations form a weak
Serre class. -/
@[stacks 093H]
#check @SheafOfModules.Localization.Basis.finitePresentationIsWeakSerreClass

/- Sieve-saturated specialization. -/
#check @SheafOfModules.Localization.Basis.finitePresentation_isWeakSerreClass
