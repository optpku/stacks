module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.NaiveComparison

/-!
# Naive cotangent comparison for morphisms of ringed topoi

The canonical comparison from the cotangent complex to the naive cotangent complex
is a quasi-isomorphism after good truncation in degrees at least `-1`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open HomologicalComplex
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

/-- The naive cotangent complex of a morphism of ringed topoi is the relative
naive cotangent complex of its inverse-image structure-sheaf map. -/
abbrev naiveCotangent
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ :=
  NaiveCotangent.obj (f.toTopos.commRingInverseImage.obj OD)
    (Under.mk (commRingStructureMap f))

/-- The notation `NL[f]` denotes the naive cotangent complex of a ringed-topos morphism. -/
scoped[RingedSite.ToposHom] notation:max "NL[" f "]" =>
  RingedSite.ToposHom.naiveCotangent f

/-- The canonical comparison from the cotangent complex of a ringed-topos morphism
to its naive cotangent complex is induced by its inverse-image structure-sheaf map. -/
abbrev toNaive
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    commRingCotangentComplex f ⟶ naiveCotangent f :=
  CotangentComplex.toNaive (f.toTopos.commRingInverseImage.obj OD)
    (Under.mk (commRingStructureMap f))

end RingedSite.ToposHom
