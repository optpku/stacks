/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
import StacksCheckRecall

/-!
# Lemma 18.19.3

The exactness of extension from a localized site is owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.Localization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J RingCat.{u}) (U : C)

/- Lemma 18.19.3 (03DJ): extension `j_{U!}` from the slice localization is exact. -/
@[stacks 03DJ]
#check
  (lowerShriek.exact R U :
    exactFunctor
      (SheafOfModules.{u} (R.over U)) (SheafOfModules.{u} R)
      (lowerShriek R U))

end SheafOfModules.Localization
