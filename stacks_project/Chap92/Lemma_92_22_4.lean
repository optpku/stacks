/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Lemma_92_22_4_NaiveCotangent
public import stacks_project.Chap92.Lemma_92_18_10_Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.NaiveComparison
import StacksCheckRecall

/-!
# Comparison of the cotangent complex of a morphism of ringed topoi with the naive cotangent complex

Lemma 92.22.4 records the canonical cochain map `L[f] ⟶ NL[f]` identifying the naive
cotangent complex with the good truncation `τ_{≥ -1} L[f]`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open HomologicalComplex
open SheafOfModules.RingedSite
open scoped RingedSite.ToposHom
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.ToposHom

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}

variable (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
  (RingedSite.ofCommRingSheaf JD OD))

/- Lemma 92.22.4. The canonical comparison identifies the naive cotangent complex
with the good truncation of the cotangent complex in degrees at least `-1`. -/
@[stacks 08V2] #check (SheafOfModules.RingedSite.CotangentComplex.toNaive_truncGE_quasiIso
    (f.toTopos.commRingInverseImage.obj OD) (Under.mk (commRingStructureMap f)) :
  QuasiIso (CochainComplex.truncGEMap (RingedSite.ToposHom.toNaive f) (-1)))

#check (RingedSite.ToposHom.toNaive f : L[f] ⟶ NL[f])

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive_zero
    (f.toTopos.commRingInverseImage.obj OD) (Under.mk (commRingStructureMap f)) :
  (RingedSite.ToposHom.toNaive f).f 0 =
    (CotangentComplex.objXIso (f.toTopos.commRingInverseImage.obj OD)
        (Under.mk (commRingStructureMap f)) 0).hom ≫
      CotangentComplex.selfDifferentials (f.toTopos.commRingInverseImage.obj OD)
        (Under.mk (commRingStructureMap f)))

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive_negOne
    (f.toTopos.commRingInverseImage.obj OD) (Under.mk (commRingStructureMap f)) :
  (RingedSite.ToposHom.toNaive f).f (-1) =
    (CotangentComplex.objXIso (f.toTopos.commRingInverseImage.obj OD)
        (Under.mk (commRingStructureMap f)) 1).hom ≫
      CotangentComplex.toConormal (f.toTopos.commRingInverseImage.obj OD)
        (Under.mk (commRingStructureMap f)))

end RingedSite.ToposHom
