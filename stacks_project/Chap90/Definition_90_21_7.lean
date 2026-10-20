module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Restriction
import StacksCheckRecall

/-!
# Restriction of groupoids in functors to a subcategory

The restriction of a groupoid in functors along a subcategory inclusion is the
groupoid in functors obtained by precomposition and left whiskering.
-/

@[expose] public section

open CategoryTheory

universe u u' v v' w

/- Definition 90.21.7: the restriction of a groupoid in functors `(U, R, s, t, c)` on `C`
to a subcategory `C'` is `GroupoidInFunctors.restrict G ι`, where `ι : C' ⥤ C` is the
inclusion (for example `ObjectProperty.ι` or `wideSubcategoryInclusion W ⋙ P.ι`).
Object and arrow functors restrict by `ι ⋙ -`, the maps `s` and `t` restrict by
`whiskerLeft ι`, and `c` is the whiskered composition transported along
`PreservesPullback.iso.inv`. -/
@[stacks 06K9]
#check (CategoryTheory.GroupoidInFunctors.restrict.{u, u', v, v', w} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
  {C' : Type u'} → [CategoryTheory.Category.{v'} C'] →
  [CategoryTheory.Limits.HasPullbacks (C' ⥤ Type w)] →
  CategoryTheory.GroupoidInFunctors.{u, v, w} C → (C' ⥤ C) →
  CategoryTheory.GroupoidInFunctors.{u', v', w} C')
