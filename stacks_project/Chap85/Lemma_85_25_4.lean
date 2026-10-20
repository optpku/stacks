module

import StacksCheckRecall
public import ReasLib.Topology.Sheaves.Simplicial.ProperDescent.GlobalSections

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject LCCat

universe u

/- Lemma 85.25.4. A proper hypercovering computes bounded-below derived global
sections through the canonical comparison for its Zariski augmentation. -/
@[stacks 09XC] #check (LCCat.rGammaPullbackComparison_app_isIso :
    ∀ {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
    [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
    [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
    [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]
    [(Sheaf.Γ (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}))]
    [(Sheaf.Γ (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]
    (ha : LCCat.IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})),
    IsIso ((CategoryTheory.SimplicialObject.rGammaPullbackComparison
      (LCCat.toTopCatAugmentation a)).app K))
