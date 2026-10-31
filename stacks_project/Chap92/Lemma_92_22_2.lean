/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.HomologyZero
import StacksCheckRecall

/-!
# Degree-zero homology of the cotangent complex of a morphism of ringed topoi

Lemma 92.22.2 identifies `H^0(L[f])` with the sheaf of relative differentials
`Ω(structureSheafMap f)` for a morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open scoped RingedSite.ToposHom
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 92.22.2. Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed
topoi. Then `H^0(L_f)` is canonically isomorphic to `Ω_f`. -/
@[stacks 08V0] #check (CategoryTheory.MorphismOfTopoiIn.cotangentComplexHomologyZeroIso :
    ∀ {C D : Type u} [Category.{u} C] [Category.{u} D]
      {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
      [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [JD.HasSheafCompose (forget RingCat.{u})]
      [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify JC CommRingCat.{u}]
      [HasWeakSheafify JC AddCommGrpCat.{u}]
      [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
      {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}
      (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
      (structureMap : (CategoryTheory.MorphismOfTopoiIn.commRingInverseImage f).obj OD ⟶ OC),
      (CategoryTheory.MorphismOfTopoiIn.cotangentComplex f structureMap).homology 0 ≅
        Ω(structureMap))

#check (CategoryTheory.MorphismOfTopoiIn.cotangentComplexHomologyZeroIso_hom :
    ∀ {C D : Type u} [Category.{u} C] [Category.{u} D]
      {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
      [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [JD.HasSheafCompose (forget RingCat.{u})]
      [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify JC CommRingCat.{u}]
      [HasWeakSheafify JC AddCommGrpCat.{u}]
      [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
      {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}
      (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
      (structureMap : (CategoryTheory.MorphismOfTopoiIn.commRingInverseImage f).obj OD ⟶ OC),
      (CategoryTheory.MorphismOfTopoiIn.cotangentComplexHomologyZeroIso f structureMap).hom =
        SheafOfModules.RingedSite.CotangentComplex.homologyZeroMap structureMap)
