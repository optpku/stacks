/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential derived limits and direct image

This file specializes preservation of sequential derived limits by total right-derived functors to
direct image on modules over ringed sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

-- Local instance justification (defeq pin): expose the existing K-injective witness
-- for the canonical direct-image functor without changing global instance search.
attribute [local instance] RingedSite.Hom.modulePushforwardToDerived.hasRightDerived

universe z uX vX uY vY w

namespace RingedSite.Hom.modulePushforwardDerived

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]

/-- Derived direct image preserves sequential derived limits whenever the underived direct image
preserves countable products and the target module category satisfies countable `AB4*`. -/
@[stacks 0A07 "derived direct image preserves sequential derived limits"]
theorem preservesDerivedLimit (f : RingedSite.Hom X Y)
    [PreservesLimitsOfShape (Discrete ℕ) f.modulePushforward]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [CountableAB4Star (ModuleCat.{z} Y)]
    {Ksys : SequentialInverseSystem (ModuleDerived.{z} X)}
    {K : ModuleDerived.{z} X} (hK : IsDerivedLimit Ksys K) :
    Nonempty
      (IsDerivedLimit (Ksys ⋙ modulePushforwardDerived.{z} f)
        ((modulePushforwardDerived.{z} f).obj K)) := sorry

end RingedSite.Hom.modulePushforwardDerived
