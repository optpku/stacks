/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.CoimageImage
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 12.3.12

Compatibility facade for the canonical coimage-image factorization.
-/

/- Lemma 12.3.12 [0107]: the canonical coimage-image comparison is the unique middle map in
the factorization of a morphism through its coimage and image. -/
@[stacks 0107]
#check @CategoryTheory.Abelian.coimageImageComparison_unique

#check @CategoryTheory.Abelian.coimageImageComparison
#check @CategoryTheory.Abelian.coimage_image_factorisation
