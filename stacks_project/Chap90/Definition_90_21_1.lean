/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors
import StacksCheckRecall

universe u v w

/- Definition 90.21.1 (1): A groupoid in functors on a category `C` is a quintuple
`(U, R, s, t, c)` of functors `U, R : C ⥤ Type w` and morphisms `s, t : R ⟶ U` and
`c : pullback s t ⟶ R` such that for every object `T` of `C`, the evaluation
`(U.obj T, R.obj T, s.app T, t.app T, c.app T)` is a groupoid category.
The identity and inverse fields encode the uniquely determined identity and
inverse operations of this quintuple, rather than additional arbitrary choices. -/
@[stacks 06K3] #check (CategoryTheory.GroupoidInFunctors.{u, v, w} :
  (C : Type u) → [CategoryTheory.Category.{v} C] → Type (max u v (w + 1)))

/- Definition 90.21.1 (2): A morphism of groupoids in functors on `C` consists of
morphisms `U ⟶ U'` and `R ⟶ R'` such that for every object `T` of `C`, the
components `U.obj T ⟶ U'.obj T` and `R.obj T ⟶ R'.obj T` define a functor of
the corresponding groupoid categories. -/
@[stacks 06K3] #check (CategoryTheory.GroupoidInFunctors.Hom.{u, v, w} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
    (G H : CategoryTheory.GroupoidInFunctors.{u, v, w} C) → Type (max u w))

/- Definition 90.21.1 (3): Groupoids in functors on `C` form a category with
the compatible maps on objects and arrows as morphisms, identity maps as
identities, and componentwise composition. The category structure is explicit. -/
@[stacks 06K3] #check (CategoryTheory.GroupoidInFunctors.category.{u, v, w} :
  (C : Type u) → [CategoryTheory.Category.{v} C] →
    CategoryTheory.Category.{max u w} (CategoryTheory.GroupoidInFunctors.{u, v, w} C))
