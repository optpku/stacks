module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Sigma
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting

/-!
# Localization at semi-representable families

A formal coproduct determines the disjoint union of its component slice sites.
Its forgetful functor and the relocalization functors induced by morphisms are
continuous, cocontinuous, and admit selected-cover lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The slice category over a member of a semi-representable family. -/
abbrev overSlice (K : FormalCoproduct.{w} C) (i : K.I) :=
  CategoryTheory.Over (K.obj i)

/-- The disjoint union of the slice categories over a semi-representable family. -/
abbrev OverSite (K : FormalCoproduct.{w} C) :=
  Σ i : K.I, overSlice K i

/-- The inclusion of a component slice into the family localization category. -/
def overIncl (K : FormalCoproduct.{w} C) (i : K.I) :
    overSlice K i ⥤ OverSite K :=
  CategoryTheory.Sigma.incl i

/-- The family localization functor assembled from the component slice forgetful functors. -/
def forget (K : FormalCoproduct.{w} C) : OverSite K ⥤ C :=
  CategoryTheory.Sigma.desc fun i ↦ CategoryTheory.Over.forget (K.obj i)

/-- Restricting the family forgetful functor to a component recovers its slice forgetful functor. -/
def forget_comp_incl (K : FormalCoproduct.{w} C) (i : K.I) :
    overIncl K i ⋙ forget K ≅ CategoryTheory.Over.forget (K.obj i) :=
  CategoryTheory.Sigma.inclDesc (fun j ↦ CategoryTheory.Over.forget (K.obj j)) i

/-- The componentwise Grothendieck topology on the disjoint union of the family slice sites. -/
def overTopology (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    GrothendieckTopology (OverSite K) :=
  CategoryTheory.Sigma.topology fun i ↦ J.over (K.obj i)

/-- A morphism of semi-representable families induces componentwise slice relocalization,
reindexing each source component by the morphism's index map. -/
def overMap {K L : FormalCoproduct.{w} C} (f : K ⟶ L) : OverSite K ⥤ OverSite L :=
  CategoryTheory.Sigma.desc fun i ↦ CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i)

/-- Restricting family relocalization to a component recovers the corresponding slice map
followed by inclusion in the target component. -/
def overMap_comp_incl {K L : FormalCoproduct.{w} C} (f : K ⟶ L) (i : K.I) :
    overIncl K i ⋙ overMap f ≅ CategoryTheory.Over.map (f.φ i) ⋙ overIncl L (f.f i) :=
  CategoryTheory.Sigma.inclDesc
    (fun j ↦ CategoryTheory.Over.map (f.φ j) ⋙ overIncl L (f.f j)) i

/-- The family localization forgetful functor is continuous for every Grothendieck topology. -/
instance forget_isContinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    (forget K).IsContinuous (overTopology J K) J :=
  sorry

/-- The family localization forgetful functor is cocontinuous for every Grothendieck topology. -/
instance forget_isCocontinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    (forget K).IsCocontinuous (overTopology J K) J :=
  sorry

/-- Selected localization covers are the families whose images under the forgetful functor
are selected covers of the original category. -/
def localizationPrecoverage (P : Precoverage C) (K : FormalCoproduct.{w} C) :
    Precoverage (OverSite K) :=
  P.comap (forget K)

/-- Localization of a selected-cover site is again a selected-cover site. -/
instance localizationPrecoverage_isSite (P : Precoverage C) [P.IsSite]
    (K : FormalCoproduct.{w} C) : (localizationPrecoverage P K).IsSite :=
  sorry

/-- The selected localization covers generate the componentwise localization topology. -/
theorem localizationPrecoverage_toGrothendieck (P : Precoverage C) [P.IsSite]
    (K : FormalCoproduct.{w} C) :
    (localizationPrecoverage P K).toGrothendieck = overTopology P.toGrothendieck K :=
  sorry

/-- The family localization forgetful functor admits relative pullbacks of selected target
covers whose source projections form selected localization covers. -/
instance forget_hasCoverLifts (P : Precoverage C) [P.IsSite] (K : FormalCoproduct.{w} C) :
    Functor.Precoverage.HasCoverLifts (forget K) (localizationPrecoverage P K) P :=
  sorry

/-- Family relocalization is continuous for every Grothendieck topology. -/
instance overMap_isContinuous (J : GrothendieckTopology C)
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    (overMap f).IsContinuous (overTopology J K) (overTopology J L) :=
  sorry

/-- Family relocalization is cocontinuous for every Grothendieck topology. -/
instance overMap_isCocontinuous (J : GrothendieckTopology C)
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    (overMap f).IsCocontinuous (overTopology J K) (overTopology J L) :=
  sorry

/-- Family relocalization admits relative pullbacks of selected target localization covers
whose source projections form selected source localization covers. -/
instance overMap_hasCoverLifts (P : Precoverage C) [P.IsSite]
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    Functor.Precoverage.HasCoverLifts (overMap f)
      (localizationPrecoverage P K) (localizationPrecoverage P L) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
