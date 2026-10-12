/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_15_1_Site

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

/-- The relocalization functor `v : OverSite K ⥤ OverSite L` induced by `f : K ⟶ L` in `SR(C)`,
sending the component `overSlice K i` into `overSlice L (f.f i)` via
`CategoryTheory.Over.map (f.φ i)`. -/
def overMap {K L : FormalCoproduct.{w} C} (f : K ⟶ L) : OverSite K ⥤ OverSite L :=
  CategoryTheory.Sigma.desc fun i ↦ CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i)

/-- Restricting `overMap f` to the `i`-th component recovers
`CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i)`. -/
def overMap_comp_incl {K L : FormalCoproduct.{w} C} (f : K ⟶ L) (i : K.I) :
    overIncl K i ⋙ overMap f ≅ CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i) :=
  CategoryTheory.Sigma.inclDesc
    (fun j ↦ CategoryTheory.Over.map (f.φ j) ⋙ overIncl L (f.f j)) i

end CategoryTheory.SemiRepresentableFamily
