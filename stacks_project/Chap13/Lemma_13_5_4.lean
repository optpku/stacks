/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.5.4

The class of morphisms inverted by an exact functor is the neutral kernel-localization API. The
canonical owner is the cone-defined system of the functor kernel, rather than a chapter-local
fraction-calculus construction.
-/

@[stacks 05R4] #check @CategoryTheory.Functor.kernel_trW_eq_inverseImage_isomorphisms

@[stacks 05R4] #check @CategoryTheory.Functor.kernel_trW_isSaturatedMultiplicativeSystem

@[stacks 05R4] #check
  @CategoryTheory.Functor.inverseImage_isomorphisms_isSaturatedMultiplicativeSystem
