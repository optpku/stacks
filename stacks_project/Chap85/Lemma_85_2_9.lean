/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.FreeAbelianResolution

/-!
# Lemma 85.2.9
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex

universe u

/- Lemma 85.2.9: the alternating-face complex of free abelian presheaves represented by
the whole stages of `X` resolves the constant integer presheaf on its diagram opens. -/
@[stacks 09W5] #check (CategoryTheory.SimplicialObject.ZariskiResolution.augmentation_quasiIso :
  ∀ (X : SimplicialObject TopCat.{u}),
    QuasiIso (CategoryTheory.SimplicialObject.ZariskiResolution.augmentation X))
