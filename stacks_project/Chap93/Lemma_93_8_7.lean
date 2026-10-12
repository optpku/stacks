/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_8_7_Localization
import StacksCheckRecall

/-!
# Localization of ring deformation categories
-/

@[expose] public section

open CategoryTheory

/- Lemma 93.8.7: in Example 93.8.1, a `k`-algebra `P` and a multiplicative subset
`S ⊆ P` induce a natural functor
`deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S)`
of deformation categories. -/
@[stacks 0DYS]
#check FlatAlgebraCat.localizationFunctor
