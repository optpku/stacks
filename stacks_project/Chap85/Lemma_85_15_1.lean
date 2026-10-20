module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import ReasLib.CategoryTheory.Sites.PrecoverageSite
public import stacks_project.Chap85.Lemma_85_15_1_Relocalization
public import stacks_project.Chap85.Lemma_85_15_1_Site
public import ReasLib.CategoryTheory.Sites.Family.Localization
import StacksCheckRecall

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

/- Lemma 85.15.1 (1): for `K` in `SR(C)`, the localization functor
`forget K : OverSite K ⥤ C` is continuous. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.forget_isContinuous :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C),
    (forget K).IsContinuous (overTopology J K) J)

/- Lemma 85.15.1 (2): for `K` in `SR(C)`, the localization functor
`forget K : OverSite K ⥤ C` is cocontinuous. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.forget_isCocontinuous :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C),
    (forget K).IsCocontinuous (overTopology J K) J)

/- The selected covering families on the localization site are the families whose
images under the forgetful functor are selected covers of the original site. -/
#check (CategoryTheory.SemiRepresentableFamily.localizationPrecoverage :
  ∀ (P : Precoverage C) (K : FormalCoproduct.{w} C), Precoverage (OverSite K))

/- Localization of a selected-cover site is again a selected-cover site. -/
#check (CategoryTheory.SemiRepresentableFamily.localizationPrecoverage_isSite :
  ∀ (P : Precoverage C) [P.IsSite] (K : FormalCoproduct.{w} C),
    (localizationPrecoverage P K).IsSite)

/- The selected localization covers generate the topology of the localization site. -/
#check (CategoryTheory.SemiRepresentableFamily.localizationPrecoverage_toGrothendieck :
  ∀ (P : Precoverage C) [P.IsSite] (K : FormalCoproduct.{w} C),
    (localizationPrecoverage P K).toGrothendieck = overTopology P.toGrothendieck K)

/- Lemma 85.15.1 (3): for `K` in `SR(C)`, the localization functor has property P
for the selected covering families of the site. Saturating to every family that
generates a covering sieve does not preserve existence of covering pullbacks. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.forget_hasCoverLifts :
  ∀ (P : Precoverage C) [P.IsSite] (K : FormalCoproduct.{w} C),
    Functor.Precoverage.HasCoverLifts (forget K) (localizationPrecoverage P K) P)

/- Lemma 85.15.1 (4): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
`overMap f : OverSite K ⥤ OverSite L` is continuous. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.overMap_isContinuous :
  ∀ (J : GrothendieckTopology C) {K L : FormalCoproduct.{w} C} (f : K ⟶ L),
    (overMap f).IsContinuous (overTopology J K) (overTopology J L))

/- Lemma 85.15.1 (5): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
`overMap f : OverSite K ⥤ OverSite L` is cocontinuous. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.overMap_isCocontinuous :
  ∀ (J : GrothendieckTopology C) {K L : FormalCoproduct.{w} C} (f : K ⟶ L),
    (overMap f).IsCocontinuous (overTopology J K) (overTopology J L))

/- Lemma 85.15.1 (6): for `f : K ⟶ L` in `SR(C)`, the relocalization functor
has property P for the selected covering families on the two localization sites. -/
@[stacks 0D85] #check (CategoryTheory.SemiRepresentableFamily.overMap_hasCoverLifts :
  ∀ (P : Precoverage C) [P.IsSite] {K L : FormalCoproduct.{w} C} (f : K ⟶ L),
    Functor.Precoverage.HasCoverLifts (overMap f)
      (localizationPrecoverage P K) (localizationPrecoverage P L))

end CategoryTheory.SemiRepresentableFamily
