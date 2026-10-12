/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionRestriction

open CategoryTheory
open SheafOfModules.RingedSite

universe u

noncomputable section

namespace RingedSite.Hom.ModuleDerived

/- Lemma 52.6.17: under flatness and the quotient comparison for a finite-type
ideal sheaf, restriction induces an equivalence on the derived-complete
categories. -/
@[stacks 099I] #check
  (RingedSite.Hom.ModuleDerived.derivedCompleteRestrictionIsEquivalence :
    ∀ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [HasSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {O O' : Sheaf J CommRingCat.{u}}
      (alpha : O ⟶ O') (I : Subobject (unitModule J O))
      [(I : ringedSiteModuleCategory J O).IsFiniteType]
      [IsFlat O ((restrictionAlong alpha).obj (unitModule J O'))]
      [IsIso (IdealSheaf.TargetQuotient.ringMap alpha I)],
      (RingedSite.Hom.ModuleDerived.derivedCompleteRestriction alpha I).IsEquivalence)

end RingedSite.Hom.ModuleDerived
