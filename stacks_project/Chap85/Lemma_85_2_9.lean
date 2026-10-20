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
