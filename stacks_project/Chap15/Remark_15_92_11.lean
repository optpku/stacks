/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
import StacksCheckRecall

@[expose] public section

/-!
# Derived completion

Remark 15.92.11 recalls the reflector onto derived-complete objects, its selected completion
functor, and the functorial unit `K ⟶ K^∧` from their canonical ReasLib owner.

@stack 0G3E
-/

#check @DerivedCategory.DerivedCompletion.Reflector
#check @DerivedCategory.DerivedCompletion.Reflector.completion
#check @DerivedCategory.DerivedCompletion.existsReflector
#check @DerivedCategory.DerivedCompletion.chosenReflector
#check @DerivedCategory.DerivedCompletion.chosenReflector_spec
#check @DerivedCategory.DerivedCompletion.chosenReflectorIso

/- Remark 15.92.11 (0G3E): the selected left adjoint is the derived-completion functor. -/
@[stacks 0G3E "derived-completion functor"]
#check @DerivedCategory.derivedCompletion

#check @DerivedCategory.derivedCompletionOf

/- Its adjunction unit is the functorial map `K ⟶ K^∧`. -/
@[stacks 0G3E "derived-completion unit"]
#check @DerivedCategory.toDerivedCompletion

#check @DerivedCategory.toDerivedCompletion_naturality
#check @DerivedCategory.derivedCompletionOf_isDerivedComplete
