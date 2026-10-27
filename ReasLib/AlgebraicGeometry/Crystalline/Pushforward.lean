/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Evaluation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.SiteSized

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Unbounded derived direct image for a morphism of ringed topoi in the
crystalline coefficient universe, using the Grothendieck module category. -/
def Ringed.derivedPushforward {X Y : RingedSite.{u + 1, u, u + 1}}
    (f : RingedSite.ToposHom X Y) : ModuleDerived.{u + 1} X ⥤ ModuleDerived.{u + 1} Y :=
  @RingedSite.ToposHom.modulePushforwardDerived X Y inferInstance inferInstance f
    inferInstance inferInstance (RingedSite.ToposHom.modulePushforwardToDerived.hasRightDerived f)

/-- Unbounded derived Zariski direct image along a scheme morphism uses the
canonical Grothendieck category of module sheaves. -/
def Ringed.derivedZariskiPushforward {T T' : Scheme.{u}} (f : T ⟶ T') :
    ModuleDerived.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski T) ⥤
      ModuleDerived.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski T') :=
  @RingedSite.Hom.modulePushforwardDerived.{u + 1} _ _ (Ringed.zariskiHom f)
    inferInstance inferInstance
    (RingedSite.Hom.modulePushforwardToDerived.hasRightDerived.{u + 1} (Ringed.zariskiHom f))

/-- Evaluation of crystalline derived direct image at a target thickening is
iterated derived direct image through the crystalline site of the inverse-image
open over the divided-power pullback and its Zariski projection. -/
theorem pushforward_eval {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec) (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    (A' : B'.ringedSite) (T : DividedPowerScheme.{u})
    (iDP : DividedPowerScheme.Hom T A'.obj.1.dividedPowerScheme)
    (πT : DividedPowerScheme.Hom T B.dividedPowerScheme)
    (hcart : DividedPowerScheme.IsPullback iDP πT (Evaluation.targetToBase B' A') g)
    (F : RingedSite.ModuleCat.{u + 1} B.ringedSite) :
    let Bᵤ := Evaluation.pullbackBase B B' g f hf A' T iDP πT hcart
    IsIsomorphic
      ((Ringed.derivedPushforward (Evaluation.evaluation B' A')).obj
        ((localizedRestrictionDerived.{u + 1} B'.ringedSite A').obj
          ((Ringed.derivedPushforward (Ringed.morphism B B' g hbase f hf)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))))
      ((Ringed.derivedZariskiPushforward iDP.base).obj
        ((Ringed.derivedPushforward (Ringed.structureMorphism Bᵤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((Evaluation.restriction B B' g f hf A' T iDP πT hcart).modulePullback.obj F)))) := sorry

end AlgebraicGeometry.Scheme.Crystalline
