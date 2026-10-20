module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.HomologyZero

/-!
# Zeroth homology of cotangent complexes of morphisms of ringed topoi

The zeroth homology of the cotangent complex is canonically isomorphic to the sheaf of
relative Kähler differentials of the inverse-image structure-sheaf map.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace CategoryTheory.MorphismOfTopoiIn

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}

/-- Zeroth homology of the cotangent complex of a morphism of ringed topoi is canonically
isomorphic to the sheaf of relative Kähler differentials of its structure-sheaf map. -/
def cotangentComplexHomologyZeroIso (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
    (structureMap : (commRingInverseImage f).obj OD ⟶ OC) :
    (cotangentComplex f structureMap).homology 0 ≅ Ω(structureMap) :=
  SheafOfModules.RingedSite.CotangentComplex.homologyZeroIso structureMap

/-- The forward morphism of the zeroth-homology isomorphism is the augmentation comparison
for the inverse-image structure-sheaf map. -/
theorem cotangentComplexHomologyZeroIso_hom (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
    (structureMap : (commRingInverseImage f).obj OD ⟶ OC) :
    (cotangentComplexHomologyZeroIso f structureMap).hom =
      SheafOfModules.RingedSite.CotangentComplex.homologyZeroMap structureMap :=
  rfl

end CategoryTheory.MorphismOfTopoiIn
