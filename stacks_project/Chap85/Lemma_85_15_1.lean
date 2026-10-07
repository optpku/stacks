module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import stacks_project.Chap85.Lemma_85_15_1_Relocalization
public import stacks_project.Chap85.Lemma_85_15_1_Site

/-!
# Lemma 85.15.1

The localization functor `j : OverSite K ⥤ C` of a semi-representable object, and the
relocalization functor `v : OverSite K ⥤ OverSite L` of a morphism in `SR(C)`, are continuous,
cocontinuous, and have property P of Sites, Remark 7.20.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SemiRepresentableFamily

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- Lemma 85.15.1 (1): for `K` in `SR(C)`, the localization functor
`forget K : OverSite K ⥤ C` is continuous. -/
@[stacks 0D85, instance]
instance forget_isContinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    (forget K).IsContinuous (overTopology J K) J :=
  sorry

/-- Lemma 85.15.1 (2): for `K` in `SR(C)`, the localization functor
`forget K : OverSite K ⥤ C` is cocontinuous. -/
@[stacks 0D85, instance]
instance forget_isCocontinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    (forget K).IsCocontinuous (overTopology J K) J :=
  sorry

/-- Lemma 85.15.1 (3): for `K` in `SR(C)`, the localization functor
`forget K : OverSite K ⥤ C` has property P of Sites, Remark 7.20.5. -/
@[stacks 0D85, instance]
instance forget_hasCoverLifts (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    Functor.Precoverage.HasCoverLifts (forget K)
      (overTopology J K).toPrecoverage J.toPrecoverage :=
  sorry

/-- Lemma 85.15.1 (4): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
`overMap f : OverSite K ⥤ OverSite L` is continuous. -/
@[stacks 0D85, instance]
instance overMap_isContinuous (J : GrothendieckTopology C)
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    (overMap f).IsContinuous (overTopology J K) (overTopology J L) :=
  sorry

/-- Lemma 85.15.1 (5): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
`overMap f : OverSite K ⥤ OverSite L` is cocontinuous. -/
@[stacks 0D85, instance]
instance overMap_isCocontinuous (J : GrothendieckTopology C)
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    (overMap f).IsCocontinuous (overTopology J K) (overTopology J L) :=
  sorry

/-- Lemma 85.15.1 (6): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
`overMap f : OverSite K ⥤ OverSite L` has property P of Sites, Remark 7.20.5. -/
@[stacks 0D85, instance]
instance overMap_hasCoverLifts (J : GrothendieckTopology C)
    {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    Functor.Precoverage.HasCoverLifts (overMap f)
      (overTopology J K).toPrecoverage (overTopology J L).toPrecoverage :=
  sorry

end CategoryTheory.SemiRepresentableFamily
