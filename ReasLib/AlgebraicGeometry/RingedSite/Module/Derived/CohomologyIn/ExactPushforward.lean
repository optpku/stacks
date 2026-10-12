/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre.Adjunction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology-in equivalences from exact pushforward

This leaf specializes weak-Serre transfer across an adjunction to modules on ringed sites.  It
then combines that target-side transfer with the bounded-basis criterion for the total derived
pullback.  The target weak-Serre certificate stays an ordinary theorem result: it is not installed
as a parameterized global instance.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe wι w z uX vX uY vY

namespace RingedSite.Hom.moduleDerivedCohomologyIn

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)
variable [UnivLE.{max uX vX, max z vX vY}]
variable [UnivLE.{max uY vY, max z vX vY}]
variable [(f.modulePushforward.{max z vX vY}).IsRightAdjoint]
variable [IsFlat.{max z vX vY} f]
variable (A' : ObjectProperty (ModuleCat.{max z vX vY} Y))
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))
variable [IsWeakSerreClass A]

/-- Lemma 21.29.1 (1) (07A8): exact pullback, an equivalence on the selected module
subcategories, exact pushforward on the source subcategory, and the underived unit criterion
transfer the weak-Serre property to the target object property. -/
@[stacks 07A8 "(1), target weak-Serre transfer"]
theorem target_isWeakSerre
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (hpush : A.map (f.modulePushforward.{max z vX vY}) ≤ A')
    (hpushExact : exactFunctor A.FullSubcategory (ModuleCat.{max z vX vY} Y)
      (A.ι ⋙ f.modulePushforward.{max z vX vY}))
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso ((modulePullbackPushforwardAdjunction.{max z vX vY} f).unit.app F'.obj)) :
    IsWeakSerreClass A' := sorry

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{max z vX vY} f)
    (ModuleQis.{max z vX vY} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{max z vX vY} f)
    (ModuleQis.{max z vX vY} Y)]
variable [DerivedAdjunction.HasPair.{max z vX vY} f]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf X.siteTopology AddCommGrpCat.{max z vX vY})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf Y.siteTopology AddCommGrpCat.{max z vX vY})]

/-- Lemma 21.29.1 (2) (07A8): after transferring the target weak-Serre property, exact
pushforward and the bounded cohomology bases promote the underived unit criterion to an
equivalence on the restricted derived categories. -/
@[stacks 07A8 "(2), derived equivalence from exact pushforward"]
theorem pullback_isEquivalence_of_exactPushforward
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (hpush : A.map (f.modulePushforward.{max z vX vY}) ≤ A')
    (hpushExact : exactFunctor A.FullSubcategory (ModuleCat.{max z vX vY} Y)
      (A.ι ⋙ f.modulePushforward.{max z vX vY}))
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso ((modulePullbackPushforwardAdjunction.{max z vX vY} f).unit.app F'.obj))
    (basisX : GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A) :
    Functor.IsEquivalence (pullbackDerived f A' A hpull) := sorry

end RingedSite.Hom.moduleDerivedCohomologyIn

end
