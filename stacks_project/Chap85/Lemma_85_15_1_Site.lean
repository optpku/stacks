/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import ReasLib.CategoryTheory.Sites.Family.Localization

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

/- The slice category of the `i`-th member of a semi-representable object `K`. -/
#check (CategoryTheory.SemiRepresentableFamily.overSlice :
  (K : FormalCoproduct.{w} C) → K.I → Type (max u v))

/- The category associated to a semi-representable object `K` in `SR(C)`: the disjoint union of
the slice categories `overSlice K i`. -/
#check (CategoryTheory.SemiRepresentableFamily.OverSite :
  FormalCoproduct.{w} C → Type (max w u v))

/- The inclusion of the `i`-th slice category into `OverSite K`. -/
#check (CategoryTheory.SemiRepresentableFamily.overIncl :
  ∀ (K : FormalCoproduct.{w} C) (i : K.I), overSlice K i ⥤ OverSite K)

/- The localization functor `j : OverSite K ⥤ C`, the coproduct of the slice forgetful functors
`CategoryTheory.Over.forget (K.obj i)`. -/
#check (CategoryTheory.SemiRepresentableFamily.forget :
  ∀ (K : FormalCoproduct.{w} C), OverSite K ⥤ C)

/- Restricting `forget K` to the `i`-th component recovers
`CategoryTheory.Over.forget (K.obj i)`. -/
#check (CategoryTheory.SemiRepresentableFamily.forget_comp_incl :
  ∀ (K : FormalCoproduct.{w} C) (i : K.I),
    overIncl K i ⋙ forget K ≅ CategoryTheory.Over.forget (K.obj i))

/- The Grothendieck topology on `OverSite K` whose covering sieves are those that restrict along
component inclusions to covering sieves of `J.over (K.obj i)`. -/
#check (CategoryTheory.SemiRepresentableFamily.overTopology :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C),
    GrothendieckTopology (OverSite K))

variable (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)

/- A sieve on an object of `OverSite K` covers iff its restriction to the component slice is a
cover for `J.over (K.obj X.1)`. -/
#check (CategoryTheory.Sigma.mem_topology_iff (fun i : K.I ↦ J.over (K.obj i)) :
  ∀ {X : OverSite K} {S : Sieve X},
    S ∈ overTopology J K X ↔
      S.functorPullback (overIncl K X.1) ∈ J.over (K.obj X.1) X.2)

end CategoryTheory.SemiRepresentableFamily
