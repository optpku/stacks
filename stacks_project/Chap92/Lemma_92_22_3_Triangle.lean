/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_22_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_8_Triangle
public import stacks_project.Chap92.Lemma_92_18_3_InverseImage
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
open scoped RingedSite.ToposHom
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

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

/-- Inverse image of commutative ring sheaves along a morphism of ringed topoi agrees with
commutative-ring inverse image of the underlying morphism of topoi. -/
theorem inverseImageCommRing_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2)) :
    inverseImageCommRing f = f.toTopos.commRingInverseImage :=
  sorry

/-- The pulled structure map `φ = f⁻¹(g♯) : f⁻¹ g⁻¹ O3 ⟶ f⁻¹ O2`. -/
def pulledBaseMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (inverseImageCommRing f).obj (inverseImageStructureSheaf g) ⟶
      inverseImageStructureSheaf f :=
  (inverseImageCommRing f).map (structureSheafMap g)

/-- Unfolding of `pulledBaseMap` as inverse image of `g♯`. -/
theorem pulledBaseMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pulledBaseMap f g = (inverseImageCommRing f).map (structureSheafMap g) :=
  sorry

/-- Finite-product transport of internal commutative rings along `g⁻¹` then `f⁻¹`. -/
def inverseImageInternalComp
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
def compositeBaseIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    inverseImageStructureSheaf (comp f g) ≅
      (inverseImageCommRing f).obj (inverseImageStructureSheaf g) :=
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
    (inverseImageCommRing f).obj (inverseImageStructureSheaf g) ⟶ OC1 :=
  pulledBaseMap f g ≫ structureSheafMap f

/-- After `compositeBaseIso`, the structure map of `g ∘ f` is `f⁻¹(g♯) ≫ f♯`. -/
theorem compositeStructureSheafMap_comp
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (compositeBaseIso f g).hom ≫ compositeAlgebraMap f g =
      structureSheafMap (comp f g) :=
  sorry

/-- Cochain-level extension of scalars of `L(f⁻¹(g♯))` along `f♯`, the underived form of
`Lf^* L[g]`. -/
abbrev pullbackCotangentCochain
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    CochainComplex (SheafOfModules (ringSheaf JC1 OC1)) ℤ :=
  CotangentComplex.tensorCochain (pulledBaseMap f g) (structureSheafMap f)

/-- Unfolding of `pullbackCotangentCochain` as `tensorCochain` of `pulledBaseMap` and
`f♯`. -/
theorem pullbackCotangentCochain_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangentCochain f g =
      CotangentComplex.tensorCochain (pulledBaseMap f g) (structureSheafMap f) :=
  sorry

/-- The first vertex `Lf^* L[g]` of the transitivity triangle, as the sheaf-level tensor
`L(f⁻¹(g♯)) ⊗^L O1`. -/
def pullbackCotangent
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    DerivedCategory (SheafOfModules (ringSheaf JC1 OC1)) :=
  CotangentComplex.tensor (pulledBaseMap f g) (structureSheafMap f)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCotangentCochain`. -/
theorem pullbackCotangent_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangent f g = DerivedCategory.Q.obj (pullbackCotangentCochain f g) :=
  sorry

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
    compositeCotangent f g = L(pulledBaseMap f g ≫ structureSheafMap f) :=
  sorry

/-- Transporting the structure map of `g ∘ f` along `compositeBaseIso` recovers the sheaf
cotangent of `f⁻¹(g♯) ≫ f♯`. -/
theorem compositeToRelativeSource_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    L((compositeBaseIso f g).hom ≫ compositeAlgebraMap f g) =
      cotangentComplex (comp f g) :=
  sorry

/-- Transporting `f⁻¹(g♯) ≫ f♯` along the inverse of `compositeBaseIso` recovers the
structure map of `g ∘ f`. -/
theorem compositeAlgebraMap_of_inv
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (compositeBaseIso f g).inv ≫ structureSheafMap (comp f g) =
      compositeAlgebraMap f g :=
  sorry

/-- Transporting the composite algebra map along the inverse of `compositeBaseIso` recovers
the sheaf cotangent of `g ∘ f`. -/
theorem relativeToCompositeSource_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    L((compositeBaseIso f g).inv ≫ structureSheafMap (comp f g)) =
      compositeCotangent f g :=
  sorry

/-- Canonical cochain identification `L[comp f g] ≅ L(f⁻¹(g♯) ≫ f♯)` induced by
`compositeBaseIso` and `compositeStructureSheafMap_comp`. -/
def compositeCotangentIso
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    cotangentComplex (comp f g) ≅ compositeCotangent f g where
  hom :=
    eqToHom (compositeToRelativeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).hom (compositeAlgebraMap f g)
  inv :=
    eqToHom (relativeToCompositeSource_eq f g).symm ≫
      CotangentComplex.toRelativeMapCochain
        (compositeBaseIso f g).inv (structureSheafMap (comp f g))
  hom_inv_id := sorry
  inv_hom_id := sorry

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
          (compositeBaseIso f g).hom (compositeAlgebraMap f g) :=
  sorry

/-- The first map `Lf^* L[g] ⟶ L[g ∘ f]` of the transitivity triangle in `D(O1)`. -/
def transitivityMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    pullbackCotangent f g ⟶ DerivedCategory.Q.obj (cotangentComplex (comp f g)) :=
  CotangentComplex.tensorMap (pulledBaseMap f g) (structureSheafMap f) ≫
    DerivedCategory.Q.map (compositeCotangentIso f g).inv

/-- Unfolding of `transitivityMap` as the sheaf-level `tensorMap` conjugated by
`compositeCotangentIso`. -/
theorem transitivityMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    transitivityMap f g =
      CotangentComplex.tensorMap (pulledBaseMap f g) (structureSheafMap f) ≫
        DerivedCategory.Q.map (compositeCotangentIso f g).inv :=
  sorry

/-- The second map `L[g ∘ f] ⟶ L[f]` of the transitivity triangle in `D(O1)`. -/
def toRelativeMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    DerivedCategory.Q.obj (cotangentComplex (comp f g)) ⟶
      DerivedCategory.Q.obj (cotangentComplex f) :=
  DerivedCategory.Q.map (compositeCotangentIso f g).hom ≫
    CotangentComplex.toRelativeMap (pulledBaseMap f g) (structureSheafMap f)

/-- Unfolding of `toRelativeMap` as the sheaf-level `toRelativeMap` conjugated by
`compositeCotangentIso`. -/
theorem toRelativeMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    toRelativeMap f g =
      DerivedCategory.Q.map (compositeCotangentIso f g).hom ≫
        CotangentComplex.toRelativeMap (pulledBaseMap f g) (structureSheafMap f) :=
  sorry

/-- The connecting map `L[f] ⟶ (Lf^* L[g])⟦1⟧` of the transitivity triangle in `D(O1)`. -/
def connectingMap
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    DerivedCategory.Q.obj (cotangentComplex f) ⟶ (pullbackCotangent f g)⟦(1 : ℤ)⟧ :=
  CotangentComplex.connectingMap (pulledBaseMap f g) (structureSheafMap f)

/-- Unfolding of `connectingMap` as the sheaf-level connecting map of `f⁻¹(g♯)` and `f♯`. -/
theorem connectingMap_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    connectingMap f g =
      CotangentComplex.connectingMap (pulledBaseMap f g) (structureSheafMap f) :=
  sorry

/-- The displayed transitivity triangle of cotangent complexes of morphisms of ringed topoi
in `D(O1)`. -/
def transitivityTriangle
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    Triangle (DerivedCategory (SheafOfModules (ringSheaf JC1 OC1))) :=
  Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g)

/-- Unfolding of `transitivityTriangle` as `Triangle.mk` of the conjugated transitivity
maps. -/
theorem transitivityTriangle_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    transitivityTriangle f g =
      Triangle.mk (transitivityMap f g) (toRelativeMap f g) (connectingMap f g) :=
  sorry

/-- The first vertex of `transitivityTriangle` is `pullbackCotangent`. -/
theorem transitivityTriangle_obj₁
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₁ = pullbackCotangent f g :=
  sorry

/-- The second vertex of `transitivityTriangle` is `Q.obj L[comp f g]`. -/
theorem transitivityTriangle_obj₂
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₂ =
      DerivedCategory.Q.obj (cotangentComplex (comp f g)) :=
  sorry

/-- The third vertex of `transitivityTriangle` is `Q.obj L[f]`. -/
theorem transitivityTriangle_obj₃
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).obj₃ = DerivedCategory.Q.obj (cotangentComplex f) :=
  sorry

/-- The first morphism of `transitivityTriangle` is `transitivityMap`. -/
theorem transitivityTriangle_mor₁
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₁ = transitivityMap f g :=
  sorry

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₂ = toRelativeMap f g :=
  sorry

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    (transitivityTriangle f g).mor₃ = connectingMap f g :=
  sorry

/-- The inverse-image target of `L[g]` along `f` is the cotangent of `f⁻¹(g♯)`. -/
theorem inverseImage_target_eq
    (f : ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)) :
    CotangentComplex.InverseImage.target f.toTopos (structureSheafMap g) =
      CotangentComplex.obj
        ((inverseImageCommRing f).obj (inverseImageStructureSheaf g))
        (Under.mk (pulledBaseMap f g)) :=
  sorry

end RingedSite.ToposHom
