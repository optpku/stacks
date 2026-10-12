/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_21_7_Restrict
import StacksCheckRecall

/-!
# Restriction of groupoids in functors to a subcategory

The restriction of a groupoid in functors along a subcategory inclusion is the
groupoid in functors obtained by precomposition and left whiskering.
-/

@[expose] public section

open CategoryTheory

/- Definition 90.21.7: the restriction of a groupoid in functors `(U, R, s, t, c)` on `C`
to a subcategory `C'` is `GroupoidInFunctors.restrict G ι`, where `ι : C' ⥤ C` is the
inclusion (for example `ObjectProperty.ι` or `wideSubcategoryInclusion W ⋙ P.ι`).
Object and arrow functors restrict by `ι ⋙ -`, the maps `s` and `t` restrict by
`whiskerLeft ι`, and `c` is the whiskered composition transported along
`PreservesPullback.iso.inv`. -/
@[stacks 06K9]
#check GroupoidInFunctors.restrict
