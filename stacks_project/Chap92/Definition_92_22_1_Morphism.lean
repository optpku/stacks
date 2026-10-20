module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complexes of morphisms of ringed topoi

This leaf specializes the sheaf-level cotangent complex to a morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, taking `L_f := L_{O_C / f⁻¹ O_D}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex

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

/-- Inverse image of commutative ring sheaves along a morphism of ringed topoi. -/
def inverseImageCommRing
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    Sheaf JD CommRingCat.{u} ⥤ Sheaf JC CommRingCat.{u} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
      (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
      f.toTopos.inverseImage inferInstance) ⋙
    InternalCommRing.fromInternal

/-- The inverse-image commutative structure sheaf `f⁻¹ O_D` of a morphism of ringed topoi. -/
def inverseImageStructureSheaf
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    Sheaf JC CommRingCat.{u} :=
  (inverseImageCommRing f).obj OD

/-- Forgetting commutativity of `f⁻¹ O_D` recovers the canonical ring-valued inverse image. -/
def inverseImageStructureSheaf_ring
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    ringSheafOfComm (inverseImageStructureSheaf f) ≅
      f.toTopos.ringInverseImage.obj (ringSheafOfComm OD) :=
  Iso.refl _

/-- The commutative-ring morphism `f♯ : f⁻¹ O_D ⟶ O_C` lifting the inverse-image structure
map of a morphism of ringed topoi. -/
def structureSheafMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    inverseImageStructureSheaf f ⟶ OC :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((inverseImageStructureSheaf_ring f).hom ≫ f.structureMap)

/-- Forgetting commutativity of `f♯` recovers the bundled inverse-image structure map. -/
theorem structureSheafMap_forget
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    ringSheafOfCommMap (structureSheafMap f) =
      (inverseImageStructureSheaf_ring f).hom ≫ f.structureMap :=
  sorry

/-- The cotangent complex of a morphism of ringed topoi is `L_{O_C / f⁻¹ O_D}`. -/
abbrev cotangentComplex
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ :=
  obj (inverseImageStructureSheaf f) (Under.mk (structureSheafMap f))

/-- Reusable notation for the cotangent complex of a morphism of ringed topoi. -/
scoped[RingedSite.ToposHom] notation:max "L[" f "]" =>
  RingedSite.ToposHom.cotangentComplex f

/-- Unfolding the cotangent complex of a morphism of ringed topoi recovers the sheaf-level
owner applied to `f♯ : f⁻¹ O_D ⟶ O_C`. -/
theorem cotangentComplex_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    cotangentComplex f =
      obj (inverseImageStructureSheaf f) (Under.mk (structureSheafMap f)) :=
  sorry

end RingedSite.ToposHom
