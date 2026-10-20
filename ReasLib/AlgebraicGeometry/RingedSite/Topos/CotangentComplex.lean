module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom

/-!
# Cotangent complexes of morphisms of ringed topoi

A geometric morphism and a map from the inverse-image commutative structure sheaf determine
an integer-indexed cochain complex of modules over the source structure sheaf.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open SheafOfModules.RingedSite

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

/-- The cotangent complex of a geometric morphism with structure map `f♯ : f⁻¹ O_D ⟶ O_C`
is the relative cotangent complex `L_{O_C / f⁻¹ O_D}`. -/
def cotangentComplex (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
    (structureMap : (commRingInverseImage f).obj OD ⟶ OC) :
    CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ :=
  CotangentComplex.obj ((commRingInverseImage f).obj OD) (Under.mk structureMap)

/-- The cotangent complex is computed by the relative cotangent construction on the
inverse-image structure-sheaf map. -/
theorem cotangentComplex_eq (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC)
    (structureMap : (commRingInverseImage f).obj OD ⟶ OC) :
    cotangentComplex f structureMap =
      CotangentComplex.obj ((commRingInverseImage f).obj OD) (Under.mk structureMap) := by rfl

end CategoryTheory.MorphismOfTopoiIn

namespace RingedSite.ToposHom

open CategoryTheory

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

/-- The commutative structure-sheaf map of a ringed-topos morphism is the fully faithful
lift of its ring-valued inverse-image structure map. -/
def commRingStructureMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    f.toTopos.commRingInverseImage.obj OD ⟶ OC :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((Iso.refl _ : ringSheafOfComm (f.toTopos.commRingInverseImage.obj OD) ≅
      f.toTopos.ringInverseImage.obj (ringSheafOfComm OD)).hom ≫ f.structureMap)

/-- Forgetting commutativity of the lifted structure map recovers the ring-valued structure
map, through the identity comparison of inverse-image ring sheaves. -/
theorem commRingStructureMap_forget
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    ringSheafOfCommMap (commRingStructureMap f) =
      (Iso.refl _ : ringSheafOfComm (f.toTopos.commRingInverseImage.obj OD) ≅
        f.toTopos.ringInverseImage.obj (ringSheafOfComm OD)).hom ≫ f.structureMap := by
  exact InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.map_preimage _

/-- The cotangent complex of a ringed-topos morphism is the relative cotangent complex of
its commutative inverse-image structure-sheaf map. -/
abbrev commRingCotangentComplex
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    CochainComplex (SheafOfModules (ringSheaf JC OC)) ℤ :=
  CategoryTheory.MorphismOfTopoiIn.cotangentComplex f.toTopos (commRingStructureMap f)

/-- The cotangent complex of a ringed-topos morphism is computed from its lifted structure
map by the relative cotangent construction. -/
theorem commRingCotangentComplex_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC OC)
      (RingedSite.ofCommRingSheaf JD OD)) :
    commRingCotangentComplex f =
      CotangentComplex.obj (f.toTopos.commRingInverseImage.obj OD)
        (Under.mk (commRingStructureMap f)) := by rfl

end RingedSite.ToposHom
