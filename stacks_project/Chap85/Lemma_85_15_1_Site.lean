/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct

/-!
# Site associated to a semi-representable object

The localization site associated to `K` in `SR(C)` is the disjoint union of the slice
categories `CategoryTheory.Over (K.obj i)`, with covering sieves inherited from the slice
topologies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The slice category of the `i`-th member of a semi-representable object `K`. -/
abbrev overSlice (K : FormalCoproduct.{w} C) (i : K.I) :=
  CategoryTheory.Over (K.obj i)

/-- The category associated to a semi-representable object `K` in `SR(C)`: the disjoint union of
the slice categories `overSlice K i`. -/
abbrev OverSite (K : FormalCoproduct.{w} C) :=
  Σ i : K.I, overSlice K i

/-- The inclusion of the `i`-th slice category into `OverSite K`. -/
def overIncl (K : FormalCoproduct.{w} C) (i : K.I) :
    overSlice K i ⥤ OverSite K :=
  CategoryTheory.Sigma.incl i

/-- The localization functor `j : OverSite K ⥤ C`, the coproduct of the slice forgetful functors
`CategoryTheory.Over.forget (K.obj i)`. -/
def forget (K : FormalCoproduct.{w} C) : OverSite K ⥤ C :=
  CategoryTheory.Sigma.desc fun i ↦ CategoryTheory.Over.forget (K.obj i)

/-- Restricting `forget K` to the `i`-th component recovers
`CategoryTheory.Over.forget (K.obj i)`. -/
def forget_comp_incl (K : FormalCoproduct.{w} C) (i : K.I) :
    overIncl K i ⋙ forget K ≅ CategoryTheory.Over.forget (K.obj i) :=
  CategoryTheory.Sigma.inclDesc (fun j ↦ CategoryTheory.Over.forget (K.obj j)) i

/-- The Grothendieck topology on `OverSite K` whose covering sieves are those that restrict along
component inclusions to covering sieves of `J.over (K.obj i)`. -/
def overTopology (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    GrothendieckTopology (OverSite K) where
  sieves X :=
    {S | S.functorPullback (overIncl K X.1) ∈ J.over (K.obj X.1) X.2}
  top_mem' := sorry
  pullback_stable' := sorry
  transitive' := sorry

/-- A sieve on an object of `OverSite K` covers iff its restriction to the component slice is a
cover for `J.over (K.obj X.1)`. -/
theorem mem_overTopology_iff {J : GrothendieckTopology C} {K : FormalCoproduct.{w} C}
    {X : OverSite K} {S : Sieve X} :
    S ∈ overTopology J K X ↔
      S.functorPullback (overIncl K X.1) ∈ J.over (K.obj X.1) X.2 :=
  sorry

end CategoryTheory.SemiRepresentableFamily
