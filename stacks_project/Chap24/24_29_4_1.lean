/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
import StacksCheckRecall

@[expose] public section

/-!
# Construction 24.29.4.1

The homotopy functor underlying `f_* Homdg(N, -)` is the induced functor of a composite of
additive functors.  The generic owner keeps the internal-Hom and pushforward choices explicit
inputs and needs no chapter-local notation or instance.
-/

@[stacks 0FTS] #check @CategoryTheory.Functor.Homotopy.comp
#check @CategoryTheory.Functor.mapHomotopyCategoryCompIso
