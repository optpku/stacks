/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_15_1_Site
public import ReasLib.CategoryTheory.Sites.Family.Localization

/-!
# Relocalization along a morphism of semi-representable objects

A morphism `f : K ⟶ L` in `SR(C)` induces `overMap f : OverSite K ⥤ OverSite L` by applying
slice relocalization on components and reindexing along `f.f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/- The relocalization functor `v : OverSite K ⥤ OverSite L` induced by `f : K ⟶ L` in `SR(C)`,
sending the component `overSlice K i` into `overSlice L (f.f i)` via
`CategoryTheory.Over.map (f.φ i)`. -/
#check (CategoryTheory.SemiRepresentableFamily.overMap :
  ∀ {K L : FormalCoproduct.{w} C} (f : K ⟶ L), OverSite K ⥤ OverSite L)

/- Restricting `overMap f` to the `i`-th component recovers
`CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i)`. -/
#check (CategoryTheory.SemiRepresentableFamily.overMap_comp_incl :
  ∀ {K L : FormalCoproduct.{w} C} (f : K ⟶ L) (i : K.I),
    overIncl K i ⋙ overMap f ≅ CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i))

end CategoryTheory.SemiRepresentableFamily
