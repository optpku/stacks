/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Cofibered.Grothendieck

/-!
# Grothendieck and discrete realizations of covariant functors

The Grothendieck and category-of-elements constructions are owned by
`ReasLib.CategoryTheory.Cofibered.Grothendieck`.
-/

@[expose] public section

namespace CategoryTheory

universe u v w vS
variable {C : Type u} [Category.{v} C]

#check (CategoryTheory.Functor.ofGroupoidValued :
  (C ⥤ Grpd.{vS, w}) → CofiberedCategoryOver.Groupoids.{u, v, max u w, max v vS} C)
#check (CategoryTheory.Functor.ofTypeValued :
  (C ⥤ Type w) → CofiberedCategoryOver.Groupoids.{u, v, max u w, v} C)
#check (CategoryTheory.Functor.ofTypeValuedMap.bijective :
  {F G : C ⥤ Type w} →
    Function.Bijective (Functor.ofTypeValuedMap : (F ⟶ G) →
      (Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)))

end CategoryTheory
