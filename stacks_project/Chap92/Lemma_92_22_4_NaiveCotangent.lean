module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.NaiveComparison

/-!
# Naive cotangent complexes of morphisms of ringed topoi

This leaf specializes the sheaf-level two-term complex to a morphism of ringed
topoi, taking `NL[f] := NL(O / f⁻¹ O_B)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite

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

#check (RingedSite.ToposHom.naiveCotangent f :
  CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ)

#check (SheafOfModules.RingedSite.CotangentComplex.naiveObj_isGE_negOne
    (f.toTopos.commRingInverseImage.obj OD) (Under.mk (commRingStructureMap f)) :
  (RingedSite.ToposHom.naiveCotangent f).IsGE (-1))

end RingedSite.ToposHom
