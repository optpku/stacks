module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

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

/-- The naive cotangent complex of a morphism of ringed topoi is
`NL(O / f⁻¹ O_B)`. -/
noncomputable abbrev naiveCotangent
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ :=
  NaiveCotangent.obj (inverseImageStructureSheaf f) (Under.mk (structureSheafMap f))

/-- Reusable notation for the naive cotangent complex of a morphism of ringed topoi. -/
scoped[RingedSite.ToposHom] notation:max "NL[" f "]" =>
  RingedSite.ToposHom.naiveCotangent f

open scoped RingedSite.ToposHom

/-- Unfolding the naive cotangent complex of a morphism of ringed topoi recovers the
sheaf-level owner applied to `f♯ : f⁻¹ O_B ⟶ O`. -/
theorem naiveCotangent_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    naiveCotangent f =
      NaiveCotangent.obj (inverseImageStructureSheaf f)
        (Under.mk (structureSheafMap f)) :=
  sorry

/-- The naive cotangent complex of a morphism of ringed topoi is concentrated in
degrees `≥ -1`. -/
instance naiveCotangent_isGE_negOne
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    (NL[f]).IsGE (-1) :=
  sorry

end RingedSite.ToposHom
