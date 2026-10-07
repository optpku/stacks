module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

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

/-- Inverse image of commutative ring sheaves along a geometric morphism of topoi. -/
def commRingInverseImage (f : MorphismOfTopoiIn.{u, u, u, u, u} JD JC) :
    Sheaf JD CommRingCat.{u} ⥤ Sheaf JC CommRingCat.{u} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
      (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
      f.inverseImage inferInstance) ⋙
    InternalCommRing.fromInternal

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
      CotangentComplex.obj ((commRingInverseImage f).obj OD) (Under.mk structureMap) := sorry

end CategoryTheory.MorphismOfTopoiIn
