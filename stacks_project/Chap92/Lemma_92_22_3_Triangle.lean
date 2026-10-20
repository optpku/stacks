module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_8_Triangle
public import stacks_project.Chap92.Lemma_92_18_3_InverseImage
public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.Transitivity

/-!
# Cotangent transitivity compatibility checks

The canonical triangle API is available through this source-side import path.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

namespace RingedSite.ToposHom

variable {C1 C2 C3 : Type u} [Category.{u} C1] [Category.{u} C2] [Category.{u} C3]
variable {JC1 : GrothendieckTopology C1} {JC2 : GrothendieckTopology C2}
variable {JC3 : GrothendieckTopology C3}
variable [JC1.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC3.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC1.HasSheafCompose (forget RingCat.{u})]
variable [JC2.HasSheafCompose (forget RingCat.{u})]
variable [JC3.HasSheafCompose (forget RingCat.{u})]
variable [JC1.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC2.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC1 CommRingCat.{u}]
variable [HasWeakSheafify JC2 CommRingCat.{u}]
variable [HasWeakSheafify JC1 AddCommGrpCat.{u}]
variable [HasWeakSheafify JC2 AddCommGrpCat.{u}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable {OC1 : Sheaf JC1 CommRingCat.{u}} {OC2 : Sheaf JC2 CommRingCat.{u}}
variable {OC3 : Sheaf JC3 CommRingCat.{u}}

/-- The legacy source presentation of the pulled structure map. -/
def pulledBaseMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (inverseImageCommRing f).obj (inverseImageStructureSheaf g) ⟶
      inverseImageStructureSheaf f :=
  pulledStructureMap f g

/-- The legacy pulled structure map is the inverse image of the source structure map. -/
theorem pulledBaseMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pulledBaseMap f g = (inverseImageCommRing f).map (structureSheafMap g) := by rfl

variable (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
  (RingedSite.ofCommRingSheaf JC2 OC2))
variable (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
  (RingedSite.ofCommRingSheaf JC3 OC3))

#check (RingedSite.ToposHom.pulledBaseMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (inverseImageCommRing f).obj (inverseImageStructureSheaf g) ⟶
      inverseImageStructureSheaf f)

#check (RingedSite.ToposHom.pulledBaseMap_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    pulledBaseMap f g = (inverseImageCommRing f).map (structureSheafMap g))

#check (RingedSite.ToposHom.pulledStructureMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)) ⟶
      (f.toTopos.commRingInverseImage.obj OC2))

#check (RingedSite.ToposHom.pulledStructureMap_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    pulledStructureMap f g = (f.toTopos.commRingInverseImage).map (commRingStructureMap g))

#check (RingedSite.ToposHom.compositeBaseIso : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    ((comp f g).toTopos.commRingInverseImage.obj OC3) ≅
      (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)))

#check (RingedSite.ToposHom.compositeAlgebraMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)) ⟶ OC1)

#check (RingedSite.ToposHom.compositeStructureSheafMap_comp : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (compositeBaseIso f g).hom ≫ compositeAlgebraMap f g =
      commRingStructureMap (comp f g))

#check (RingedSite.ToposHom.pullbackCotangentCochain : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ)

#check (RingedSite.ToposHom.pullbackCotangentCochain_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    pullbackCotangentCochain f g =
      CotangentComplex.tensorCochain (pulledBaseMap f g) (commRingStructureMap f))

#check (RingedSite.ToposHom.pullbackCotangent : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    RingedSiteDerived JC1 OC1)

#check (RingedSite.ToposHom.pullbackCotangent_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    pullbackCotangent f g = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (pullbackCotangentCochain f g))

#check (Eq.refl (pullbackCotangent f g) :
    pullbackCotangent f g =
      CotangentComplex.tensor ((inverseImageCommRing f).map (structureSheafMap g))
        (structureSheafMap f))

#check (RingedSite.ToposHom.compositeCotangent : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ)

#check (RingedSite.ToposHom.compositeCotangent_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    compositeCotangent f g = L(pulledBaseMap f g ≫ commRingStructureMap f))

#check (RingedSite.ToposHom.compositeToRelativeSource_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    L((compositeBaseIso f g).hom ≫ compositeAlgebraMap f g) =
      commRingCotangentComplex (comp f g))

#check (RingedSite.ToposHom.compositeAlgebraMap_of_inv : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (compositeBaseIso f g).inv ≫ commRingStructureMap (comp f g) =
      compositeAlgebraMap f g)

#check (RingedSite.ToposHom.relativeToCompositeSource_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    L((compositeBaseIso f g).inv ≫ commRingStructureMap (comp f g)) =
      compositeCotangent f g)

#check (RingedSite.ToposHom.compositeCotangentIso_hom_inv_id : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)) ≫
    (eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (commRingStructureMap (comp f g))) = 𝟙 (commRingCotangentComplex (comp f g)))

#check (RingedSite.ToposHom.compositeCotangentIso_inv_hom_id : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (commRingStructureMap (comp f g))) ≫
    (eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)) = 𝟙 (compositeCotangent f g))

#check (RingedSite.ToposHom.compositeCotangentIso : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    commRingCotangentComplex (comp f g) ≅ compositeCotangent f g)

#check (RingedSite.ToposHom.compositeCotangentIso_hom_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (compositeCotangentIso f g).hom =
      eqToHom (compositeToRelativeSource_eq f g).symm ≫
        CotangentComplex.toRelativeMapCochain
          (compositeBaseIso f g).hom (compositeAlgebraMap f g))

#check (RingedSite.ToposHom.transitivityMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    pullbackCotangent f g ⟶ (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)))

#check (RingedSite.ToposHom.transitivityMap_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    transitivityMap f g =
      CotangentComplex.tensorMap (pulledBaseMap f g) (commRingStructureMap f) ≫
        (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).inv)

#check (RingedSite.ToposHom.toRelativeMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)) ⟶
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f))

#check (RingedSite.ToposHom.toRelativeMap_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    toRelativeMap f g =
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).hom ≫
        CotangentComplex.toRelativeMap (pulledBaseMap f g) (commRingStructureMap f))

#check (RingedSite.ToposHom.connectingMap : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f) ⟶ (pullbackCotangent f g)⟦(1 : ℤ)⟧)

#check (RingedSite.ToposHom.connectingMap_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    connectingMap f g =
      CotangentComplex.connectingMap (pulledBaseMap f g) (commRingStructureMap f))

#check (Eq.refl (connectingMap f g) :
    connectingMap f g =
      CotangentComplex.connectingMap ((inverseImageCommRing f).map (structureSheafMap g))
        (structureSheafMap f))

#check (RingedSite.ToposHom.transitivityTriangle : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    Triangle (RingedSiteDerived JC1 OC1))

#check (RingedSite.ToposHom.transitivityTriangle_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    transitivityTriangle f g =
      Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g))

#check (RingedSite.ToposHom.transitivityTriangle_obj₁ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).obj₁ = pullbackCotangent f g)

#check (RingedSite.ToposHom.transitivityTriangle_obj₂ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).obj₂ =
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)))

#check (RingedSite.ToposHom.transitivityTriangle_obj₃ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).obj₃ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f))

#check (RingedSite.ToposHom.transitivityTriangle_mor₁ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).mor₁ = transitivityMap f g)

#check (RingedSite.ToposHom.transitivityTriangle_mor₂ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).mor₂ = toRelativeMap f g)

#check (RingedSite.ToposHom.transitivityTriangle_mor₃ : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    (transitivityTriangle f g).mor₃ = connectingMap f g)

#check (RingedSite.ToposHom.inverseImage_target_eq : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    CotangentComplex.InverseImage.target f.toTopos (commRingStructureMap g) =
      CotangentComplex.obj
        ((f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)))
        (Under.mk (pulledBaseMap f g)))

#check (RingedSite.ToposHom.transitivityTriangle_distinguished : ∀
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    transitivityTriangle f g ∈ distTriang (RingedSiteDerived JC1 OC1))

/- The shared lifted structure map agrees definitionally with the source presentation. -/
#check (Eq.refl (commRingStructureMap f) : structureSheafMap f = commRingStructureMap f)

/- The shared cotangent complex agrees definitionally with the source presentation. -/
#check (Eq.refl (commRingCotangentComplex f) : cotangentComplex f = commRingCotangentComplex f)

end RingedSite.ToposHom
