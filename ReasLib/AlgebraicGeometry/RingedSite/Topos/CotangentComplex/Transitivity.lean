module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentInverseImage
public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Transitivity triangle of cotangent complexes of morphisms of ringed topoi

For morphisms of ringed topoi `f` and `g`, this module owns the displayed triangle
`Lf^* L[g] ⟶ L[g ∘ f] ⟶ L[f] ⟶ (Lf^* L[g])⟦1⟧` in `D(O1)`. The sheaf-level
transitivity triangle of `f⁻¹(g♯)` and `f♯` is conjugated along `compositeCotangentIso`
so that the middle vertex is `Q.obj L[comp f g]`.
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

/-- The pulled structure map `φ = f⁻¹(g♯) : f⁻¹ g⁻¹ O3 ⟶ f⁻¹ O2`. -/
def pulledStructureMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)) ⟶
      (f.toTopos.commRingInverseImage.obj OC2) :=
  (f.toTopos.commRingInverseImage).map (commRingStructureMap g)

/-- Unfolding of `pulledStructureMap` as inverse image of `g♯`. -/
theorem pulledStructureMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pulledStructureMap f g = (f.toTopos.commRingInverseImage).map (commRingStructureMap g) := by rfl

/-- Finite-product transport of internal commutative rings along `g⁻¹` then `f⁻¹`. -/
private def inverseImageInternalComp
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    @mapCommRingOfFiniteProducts (Sheaf JC3 (Type u)) _ _
        (sheafBraidedCategory JC3) (Sheaf JC1 (Type u)) _ _
        (sheafBraidedCategory JC1)
        (g.toTopos.inverseImage ⋙ f.toTopos.inverseImage) inferInstance ≅
      @mapCommRingOfFiniteProducts (Sheaf JC3 (Type u)) _ _
          (sheafBraidedCategory JC3) (Sheaf JC2 (Type u)) _ _
          (sheafBraidedCategory JC2) g.toTopos.inverseImage inferInstance ⋙
        @mapCommRingOfFiniteProducts (Sheaf JC2 (Type u)) _ _
          (sheafBraidedCategory JC2) (Sheaf JC1 (Type u)) _ _
          (sheafBraidedCategory JC1) f.toTopos.inverseImage inferInstance :=
  @mapCommRingOfFiniteProductsCompIso (Sheaf JC3 (Type u)) _ _
    (sheafBraidedCategory JC3) (Sheaf JC2 (Type u)) _ _
    (sheafBraidedCategory JC2) (Sheaf JC1 (Type u)) _ _
    (sheafBraidedCategory JC1) g.toTopos.inverseImage inferInstance
    f.toTopos.inverseImage inferInstance

/-- Canonical identification `(g ∘ f)⁻¹ O3 ≅ f⁻¹ g⁻¹ O3` of commutative ring sheaves. -/
@[no_expose] def compositeBaseIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    ((comp f g).toTopos.commRingInverseImage.obj OC3) ≅
      (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)) :=
  fromInternal.mapIso
      ((inverseImageInternalComp f g).app (toInternal.obj OC3)) ≪≫
    fromInternal.mapIso
      ((@mapCommRingOfFiniteProducts (Sheaf JC2 (Type u)) _ _
          (sheafBraidedCategory JC2) (Sheaf JC1 (Type u)) _ _
          (sheafBraidedCategory JC1) f.toTopos.inverseImage inferInstance).mapIso
        (fromToIso.symm.app
          ((@mapCommRingOfFiniteProducts (Sheaf JC3 (Type u)) _ _
              (sheafBraidedCategory JC3) (Sheaf JC2 (Type u)) _ _
              (sheafBraidedCategory JC2) g.toTopos.inverseImage inferInstance).obj
            (toInternal.obj OC3))))

/-- The composite algebra map `f⁻¹(g♯) ≫ f♯` on `C1`. -/
abbrev compositeAlgebraMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)) ⟶ OC1 :=
  pulledStructureMap f g ≫ commRingStructureMap f

/-- After `compositeBaseIso`, the structure map of `g ∘ f` is `f⁻¹(g♯) ≫ f♯`. -/
theorem compositeStructureSheafMap_comp
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (compositeBaseIso f g).hom ≫ compositeAlgebraMap f g =
      commRingStructureMap (comp f g) :=
  sorry

/-- Cochain-level extension of scalars of `L(f⁻¹(g♯))` along `f♯`, the underived form of
`Lf^* L[g]`. -/
abbrev pullbackCotangentCochain
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ :=
  CotangentComplex.tensorCochain (pulledStructureMap f g) (commRingStructureMap f)

/-- Unfolding of `pullbackCotangentCochain` as `tensorCochain` of `pulledStructureMap` and
`f♯`. -/
theorem pullbackCotangentCochain_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangentCochain f g =
      CotangentComplex.tensorCochain (pulledStructureMap f g) (commRingStructureMap f) := by rfl

/-- The first vertex `Lf^* L[g]` of the transitivity triangle, as the sheaf-level tensor
`L(f⁻¹(g♯)) ⊗^L O1`. -/
def pullbackCotangent
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    RingedSiteDerived JC1 OC1 :=
  CotangentComplex.tensor (pulledStructureMap f g) (commRingStructureMap f)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCotangentCochain`. -/
theorem pullbackCotangent_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangent f g = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (pullbackCotangentCochain f g) := by rfl

/-- The cotangent of the composite algebra map `f⁻¹(g♯) ≫ f♯`, i.e. the sheaf-level
form of `L[g ∘ f]` after `compositeBaseIso`. -/
abbrev compositeCotangent
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ :=
  L(compositeAlgebraMap f g)

/-- Unfolding of `compositeCotangent` as the sheaf cotangent of `compositeAlgebraMap`. -/
theorem compositeCotangent_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    compositeCotangent f g = L(pulledStructureMap f g ≫ commRingStructureMap f) := by rfl

/-- Transporting the structure map of `g ∘ f` along `compositeBaseIso` recovers the sheaf
cotangent of `f⁻¹(g♯) ≫ f♯`. -/
theorem compositeToRelativeSource_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    L((compositeBaseIso f g).hom ≫ compositeAlgebraMap f g) =
      commRingCotangentComplex (comp f g) :=
  sorry

/-- Transporting `f⁻¹(g♯) ≫ f♯` along the inverse of `compositeBaseIso` recovers the
structure map of `g ∘ f`. -/
theorem compositeAlgebraMap_of_inv
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (compositeBaseIso f g).inv ≫ commRingStructureMap (comp f g) =
      compositeAlgebraMap f g :=
  sorry

/-- Transporting the composite algebra map along the inverse of `compositeBaseIso` recovers
the sheaf cotangent of `g ∘ f`. -/
theorem relativeToCompositeSource_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    L((compositeBaseIso f g).inv ≫ commRingStructureMap (comp f g)) =
      compositeCotangent f g :=
  sorry

/-- Forward and reverse change of the base structure sheaf compose to the identity on
the cotangent complex of the composite ringed-topos morphism. -/
theorem compositeCotangentIso_hom_inv_id
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)) ≫
    (eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (commRingStructureMap (comp f g))) = 𝟙 (commRingCotangentComplex (comp f g)) :=
  sorry

/-- Reverse and forward change of the base structure sheaf compose to the identity on
the cotangent complex of the composite algebra map. -/
theorem compositeCotangentIso_inv_hom_id
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (commRingStructureMap (comp f g))) ≫
    (eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)) = 𝟙 (compositeCotangent f g) :=
  sorry

/-- Canonical cochain identification `L[comp f g] ≅ L(f⁻¹(g♯) ≫ f♯)` induced by
`compositeBaseIso` and `compositeStructureSheafMap_comp`. -/
def compositeCotangentIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    commRingCotangentComplex (comp f g) ≅ compositeCotangent f g where
  hom :=
    eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)
  inv :=
    eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (commRingStructureMap (comp f g))
  hom_inv_id := compositeCotangentIso_hom_inv_id f g
  inv_hom_id := compositeCotangentIso_inv_hom_id f g

/-- Unfolding of `compositeCotangentIso` as base change of sheaf cotangents along
`compositeBaseIso`. -/
theorem compositeCotangentIso_hom_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (compositeCotangentIso f g).hom =
      eqToHom (compositeToRelativeSource_eq f g).symm ≫
        CotangentComplex.toRelativeMapCochain
          (compositeBaseIso f g).hom (compositeAlgebraMap f g) := by rfl

/-- The first map `Lf^* L[g] ⟶ L[g ∘ f]` of the transitivity triangle in `D(O1)`. -/
def transitivityMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangent f g ⟶ (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)) :=
  CotangentComplex.tensorMap (pulledStructureMap f g) (commRingStructureMap f) ≫
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).inv

/-- Unfolding of `transitivityMap` as the sheaf-level `tensorMap` conjugated by
`compositeCotangentIso`. -/
theorem transitivityMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    transitivityMap f g =
      CotangentComplex.tensorMap (pulledStructureMap f g) (commRingStructureMap f) ≫
        (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).inv := by rfl

/-- The second map `L[g ∘ f] ⟶ L[f]` of the transitivity triangle in `D(O1)`. -/
def toRelativeMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)) ⟶
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f) :=
  (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).hom ≫
    CotangentComplex.toRelativeMap (pulledStructureMap f g) (commRingStructureMap f)

/-- Unfolding of `toRelativeMap` as the sheaf-level `toRelativeMap` conjugated by
`compositeCotangentIso`. -/
theorem toRelativeMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    toRelativeMap f g =
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).map (compositeCotangentIso f g).hom ≫
        CotangentComplex.toRelativeMap (pulledStructureMap f g) (commRingStructureMap f) := by rfl

/-- The connecting map `L[f] ⟶ (Lf^* L[g])⟦1⟧` of the transitivity triangle in `D(O1)`. -/
def connectingMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f) ⟶ (pullbackCotangent f g)⟦(1 : ℤ)⟧ :=
  CotangentComplex.connectingMap (pulledStructureMap f g) (commRingStructureMap f)

/-- Unfolding of `connectingMap` as the sheaf-level connecting map of `f⁻¹(g♯)` and `f♯`. -/
theorem connectingMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    connectingMap f g =
      CotangentComplex.connectingMap (pulledStructureMap f g) (commRingStructureMap f) := by rfl

/-- The displayed transitivity triangle of cotangent complexes of morphisms of ringed topoi
in `D(O1)`. -/
def transitivityTriangle
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    Triangle (RingedSiteDerived JC1 OC1) :=
  Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g)

/-- Unfolding of `transitivityTriangle` as `Triangle.mk` of the conjugated transitivity
maps. -/
theorem transitivityTriangle_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    transitivityTriangle f g =
      Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g) := by rfl

/-- The first vertex of `transitivityTriangle` is `pullbackCotangent`. -/
theorem transitivityTriangle_obj₁
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₁ = pullbackCotangent f g := by rfl

/-- The second vertex of `transitivityTriangle` is `Q.obj L[comp f g]`. -/
theorem transitivityTriangle_obj₂
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₂ =
      (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex (comp f g)) := by rfl

/-- The third vertex of `transitivityTriangle` is `Q.obj L[f]`. -/
theorem transitivityTriangle_obj₃
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₃ = (@DerivedCategory.Q _ inferInstance inferInstance
      (moduleCategoryHasDerivedCategory (𝒪 := OC1))).obj (commRingCotangentComplex f) := by rfl

/-- The first morphism of `transitivityTriangle` is `transitivityMap`. -/
theorem transitivityTriangle_mor₁
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₁ = transitivityMap f g := by rfl

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₂ = toRelativeMap f g := by rfl

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₃ = connectingMap f g := by rfl

/-- The inverse-image target of `L[g]` along `f` is the cotangent of `f⁻¹(g♯)`. -/
theorem inverseImage_target_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    CotangentComplex.InverseImage.target f.toTopos (commRingStructureMap g) =
      CotangentComplex.obj
        ((f.toTopos.commRingInverseImage).obj ((g.toTopos.commRingInverseImage.obj OC3)))
        (Under.mk (pulledStructureMap f g)) := by rfl

/-- The canonical cotangent transitivity triangle of two composable morphisms of ringed
topoi is distinguished in the derived category of modules over the source structure sheaf. -/
theorem transitivityTriangle_distinguished
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    transitivityTriangle f g ∈ distTriang (RingedSiteDerived JC1 OC1) :=
  sorry

end RingedSite.ToposHom
