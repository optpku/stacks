/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.ExternalTensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.9 (08QB) is recalled from the reusable product-site lower-shriek owner.  Its
source sheaf notation is represented there by the canonical chaotic-site module-presheaf model.
-/

@[stacks 08QB]
#check @CategoryTheory.DerivedColimit.ExternalTensor.tensorProjectionInverseImages_isomorphic
