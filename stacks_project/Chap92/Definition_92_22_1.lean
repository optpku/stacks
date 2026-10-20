/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Definition 92.22.1: Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a
morphism of ringed topoi. The cotangent complex `L_f` of `f` is
`L_f = L_{O_C / f⁻¹ O_D}`. We sometimes write `L_f = L_{O_C / O_D}`. -/
@[stacks 08SU]
#check (CategoryTheory.MorphismOfTopoiIn.cotangentComplex :
  ∀ {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [JD.HasSheafCompose (forget RingCat.{u})]
    [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JC AddCommGrpCat.{u}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
    {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}},
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC) →
      ((CategoryTheory.MorphismOfTopoiIn.commRingInverseImage f).obj OD ⟶ OC) →
        CochainComplex (SheafOfModules (SheafOfModules.RingedSite.ringSheaf JC OC)) ℤ)
