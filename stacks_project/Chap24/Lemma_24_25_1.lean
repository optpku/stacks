/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.InjectiveTest
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.25.1

The canonical family is indexed by subobjects of the separator of the graded module category.
Its concrete source, target, arrow, monomorphism, and extension criterion live in the neutral
`Graded.Module.InjectiveTest` leaf.
-/

open CategoryTheory

/- Lemma 24.25.1: a set-sized family of monomorphisms detects injective graded modules by the
   extension property. -/
#check @InjectiveTest.index
#check @InjectiveTest.source
#check @InjectiveTest.target
#check @InjectiveTest.arrow
#check @InjectiveTest.arrow_mono
@[stacks 0FSN] #check @InjectiveTest.injective_iff_lifts
#check @InjectiveTest.exists_family
