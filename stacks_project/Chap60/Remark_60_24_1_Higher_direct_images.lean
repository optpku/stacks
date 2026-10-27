/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

/- Remark 60.24.1 (Higher direct images): for a compatible morphism of
prime-local divided-power bases and a commuting square of source schemes with
locally nilpotent prime, evaluation of the crystalline derived direct image of
a module at a target thickening is the iterated crystalline structure direct
image over the divided-power pullback followed by its Zariski direct image.
The module is embedded in degree zero, and its restriction is taken on the
crystalline site of the inverse-image open. -/
@[stacks 07MJ] #check (AlgebraicGeometry.Scheme.Crystalline.pushforward_eval :
  ∀ {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec) (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    (A' : B'.ringedSite) (T : DividedPowerScheme.{u})
    (iDP : DividedPowerScheme.Hom T A'.obj.1.dividedPowerScheme)
    (πT : DividedPowerScheme.Hom T B.dividedPowerScheme)
    (hcart : DividedPowerScheme.IsPullback iDP πT (Evaluation.targetToBase B' A') g)
    (F : RingedSite.ModuleCat.{u + 1} B.ringedSite),
    let Bᵤ := Evaluation.pullbackBase B B' g f hf A' T iDP πT hcart
    IsIsomorphic
      ((Ringed.derivedPushforward (Evaluation.evaluation B' A')).obj
        ((localizedRestrictionDerived.{u + 1} B'.ringedSite A').obj
          ((Ringed.derivedPushforward (Ringed.morphism B B' g hbase f hf)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))))
      ((Ringed.derivedZariskiPushforward iDP.base).obj
        ((Ringed.derivedPushforward (Ringed.structureMorphism Bᵤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((Evaluation.restriction B B' g f hf A' T iDP πT hcart).modulePullback.obj F)))))
