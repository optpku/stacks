module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
import StacksCheckRecall

/-!
# Lemma 18.19.4

Exactness preservation and reflection for extension from a localized site are owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.Localization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J RingCat.{u}) (U : C)
variable (S : ShortComplex (SheafOfModules.{u} (R.over U)))

/- Lemma 18.19.4 (0E8G): a short complex on the slice localization is exact if and only if
its extension `j_{U!}` to the ambient site is exact. -/
@[stacks 0E8G]
#check
  (lowerShriek.exactMapIff R U S :
    S.Exact ↔
      (S.map (lowerShriek R U :
        SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)).Exact)

end SheafOfModules.Localization
