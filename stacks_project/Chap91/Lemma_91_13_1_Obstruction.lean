/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.MapObstruction

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{u}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
variable [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2]

/-- The derived-category quotient of cochain complexes of `𝒪`-modules. -/
abbrev moduleQ (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J O) ℤ ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J O) :=
  DerivedCategory.Q

variable (D : RelativeDiagram πO1 πB1 πO2 πB2)

/- Lemma 91.13.1: the canonical common-site obstruction. -/
#check (mapObstruction D :
  Ext⁽(1 : ℤ)⁾(
    (SameSite.pullbackDerived D.g).obj
      (DerivedCategory.Q.obj (NaiveCotangent.obj OB1 (Under.mk D.f1))),
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J O2) 0).obj
        (ideal πO2))))

#check (homOmegaPushforwardEquiv :
  (Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) ≃
    ((extendAlong D.g).obj Ω(D.f1) ⟶ ideal πO2))

#check (homOmegaExtZero_bijective.{u, u, u} : Function.Bijective
  (fun α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2) ↦
    homOmegaExtZero.{u, u, u} α))

end SheafOfModules.RingedSite.FirstOrderThickening
