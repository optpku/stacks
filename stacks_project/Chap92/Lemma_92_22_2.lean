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

/-- Lemma 92.22.2. Let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of ringed
topoi. Then `H^0(L[f]) = Ω(structureSheafMap f)`. -/
abbrev homologyZeroIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    L[f].homology 0 ≅ Ω(structureSheafMap f) :=
  CategoryTheory.MorphismOfTopoiIn.cotangentComplexHomologyZeroIso f.toTopos
    (structureSheafMap f)

end RingedSite.ToposHom
