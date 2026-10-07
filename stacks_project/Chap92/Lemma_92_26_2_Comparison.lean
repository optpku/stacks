module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import stacks_project.Chap92.«92_28_0_1_Transitivity»
public import stacks_project.Chap66.Lemma_66_26_1_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

/-!
# Étale restriction of cotangent complexes of algebraic spaces

For a commutative square of algebraic spaces with étale vertical maps, this module
owns the identifications `g⁻¹ 𝒪_V ≅ p⁻¹(f⁻¹ 𝒪_Y)` and
`pullbackCotangent p f ≅ cotangent g` in `D(𝒪_U)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Modules
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable {S : Scheme.{u}}

/-- Canonical braiding of type-valued sheaves on a small étale site. -/
instance (priority := high) smallEtaleTypeSheafBraided (X : AlgebraicSpace S) :
    BraidedCategory (Sheaf (smallEtaleTopology X) (Type u)) :=
  sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X)

/-- The lifted structure map of an étale morphism of algebraic spaces is an isomorphism,
so `h_small⁻¹ 𝒪_Y = 𝒪_X` after universe lift. -/
instance structureMapLift_isIso {X Y : AlgebraicSpace S} (h : X ⟶ Y) [Etale h] :
    IsIso (structureMapLift h) :=
  sorry

/-- The lifted structure map is an isomorphism if and only if the unlifted inverse-image
structure map of `ringedToposHom h` is an isomorphism. -/
theorem structureMapLift_isIso_iff {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    IsIso (structureMapLift h) ↔ IsIso (ringedToposHom h).structureMap :=
  sorry

/-- Universe lift of an isomorphism of commutative-ring sheaves on the small étale site. -/
def liftSheafIso (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    liftSheafObj X R ≅ liftSheafObj X R' where
  hom := liftSheafMap X e.hom
  inv := liftSheafMap X e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying maps of `liftSheafIso` are `liftSheafMap` of the unlifted iso. -/
theorem liftSheafIso_hom (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    (liftSheafIso X e).hom = liftSheafMap X e.hom :=
  sorry

/-- Inverse image of types along a composite morphism of algebraic spaces. -/
def inverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    (morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage ≅
      (morphismOfTopoi (p ≫ f)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
    (morphismOfTopoi (p ≫ f)).adjunction (typePushforwardComp p f)

/-- Inverse image of internal commutative rings reassociates along composition. -/
def internalCommRingInverseImageCompIso {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    internalCommRingInverseImage f ⋙ internalCommRingInverseImage p ≅
      internalCommRingInverseImage (p ≫ f) :=
  (@mapCommRingOfFiniteProductsCompIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      (morphismOfTopoi f).inverseImage inferInstance
      (morphismOfTopoi p).inverseImage inferInstance).symm ≪≫
    @mapCommRingOfFiniteProductsNatIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      ((morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage)
      (morphismOfTopoi (p ≫ f)).inverseImage inferInstance inferInstance
      (inverseImageCompIso p f)

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def commSheafInverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageObj p (commSheafInverseImageObj f R) ≅
      commSheafInverseImageObj (p ≫ f) R :=
  fromInternal.{u + 1, u, u}.mapIso
    ((internalCommRingInverseImage p).mapIso
        (fromToIso.{u + 1, u, u}.app
          ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
      (internalCommRingInverseImageCompIso p f).app
        (toInternalObj.{u + 1, u, u} R))

/-- Inverse image of an isomorphism of commutative-ring sheaves. -/
def commSheafInverseImageMapIso {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (e : R ≅ R') :
    commSheafInverseImageObj h R ≅ commSheafInverseImageObj h R' where
  hom := commSheafInverseImageMap h e.hom
  inv := commSheafInverseImageMap h e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- For an étale morphism, `h^♯ : h⁻¹ 𝒪_Y ⟶ 𝒪_X` is an isomorphism of commutative-ring
sheaves. -/
instance commInverseImageStructureSheafMap_isIso {X Y : AlgebraicSpace S}
    (h : X ⟶ Y) [Etale h] : IsIso (commInverseImageStructureSheafMap h) :=
  sorry

/-- For an étale morphism, the inverse-image form `h⁻¹ 𝒪_Y` identifies with `𝒪_X`. -/
def commInverseImageStructureSheafIso_of_etale {X Y : AlgebraicSpace S}
    (h : X ⟶ Y) [Etale h] :
    commInverseImageStructureSheaf h ≅ commStructureSheaf X :=
  asIso (commInverseImageStructureSheafMap h)

/-- Unlifted identification `g⁻¹ 𝒪_V ≅ p⁻¹(f⁻¹ 𝒪_Y)` of an étale commutative square. -/
irreducible_def inverseImageCommSqUnliftedIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    commInverseImageStructureSheaf g ≅
      commSheafInverseImageObj p (commInverseImageStructureSheaf f) :=
  commSheafInverseImageMapIso g
      (commInverseImageStructureSheafIso_of_etale q).symm ≪≫
    commSheafInverseImageCompIso g q (commStructureSheaf Y) ≪≫
    eqToIso (congrArg
      (fun h : U ⟶ Y ↦ commSheafInverseImageObj h (commStructureSheaf Y)) sq.w) ≪≫
    (commSheafInverseImageCompIso p f (commStructureSheaf Y)).symm

/-- The identification `g_small⁻¹ 𝒪_V ≅ p_small⁻¹ f_small⁻¹ 𝒪_Y` induced by an étale
commutative square. -/
irreducible_def inverseImageCommSqIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    inverseImageLift g ≅ pulledInverseImage p f :=
  liftSheafIso U (inverseImageCommSqUnliftedIso p q g f sq)

/-- `inverseImageCommSqIso` is the universe lift of `inverseImageCommSqUnliftedIso`. -/
theorem inverseImageCommSqIso_eq {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    inverseImageCommSqIso p q g f sq =
      liftSheafIso U (inverseImageCommSqUnliftedIso p q g f sq) :=
  sorry

/-- After the inverse-image identification of an étale square, `g^♯` is the composite
`p⁻¹(f^♯) ≫ p^♯`. -/
theorem compositeStructureMap_eq {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    (inverseImageCommSqIso p q g f sq).hom ≫ compositeStructureMap p f =
      structureMapLift g :=
  sorry

/-- Inverse form of `compositeStructureMap_eq`. -/
theorem compositeStructureMap_eq_inv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    (inverseImageCommSqIso p q g f sq).inv ≫ structureMapLift g =
      compositeStructureMap p f :=
  sorry

/-- Structure-map square used to compare standard-resolution terms of `g^♯` and the
composite algebra map, after `inverseImageCommSqIso.inv`. -/
theorem etaleRestrictTerm_w {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    (inverseImageCommSqIso p q g f sq).inv ≫ structureMapLift g =
      compositeStructureMap p f ≫ 𝟙 (commStructureSheafLift U) :=
  sorry

/-- Structure-map square used to compare standard-resolution terms of the composite algebra
map and `g^♯`, after `inverseImageCommSqIso.hom`. -/
theorem etaleRestrictTerm_w_hom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    (inverseImageCommSqIso p q g f sq).hom ≫ compositeStructureMap p f =
      structureMapLift g ≫ 𝟙 (commStructureSheafLift U) :=
  sorry

/-- Along an étale morphism, extension of scalars of the pulled cotangent complex is an
isomorphism onto the composite cotangent. -/
instance transitivityMapCochain_isIso {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) [Etale p] :
    IsIso (transitivityMapCochain p f) :=
  sorry

/-- The map of simplicial cotangent modules induced by a change of base over a fixed
target ring sheaf. -/
def baseChangeSimplicialHom {X : AlgebraicSpace S}
    {A A' O : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : A ⟶ A') (φ : A ⟶ O) (φ' : A' ⟶ O)
    (hα : α ≫ φ' = φ ≫ 𝟙 O) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A (Under.mk φ)).obj n ⟶
      (simplicialModule A' (Under.mk φ')).obj n :=
  ((extendRestrictAdj (standardAugmentation A (Under.mk φ) n)).homEquiv _ _).symm
    (RelativeDifferentials.map.{u + 1, u, u + 1} (C := smallEtaleSite X) (J := smallEtaleTopology X)
        ⟨standardTermRightHom_square (B := Under.mk φ) (B' := Under.mk φ')
          α (𝟙 O) hα n⟩ ≫
      (restrictAlong (standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ')
          α (𝟙 O) n)).map
        ((extendRestrictAdj (standardAugmentation A' (Under.mk φ') n)).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringOfMap (standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ')
            α (𝟙 O) n))
          (ringOfMap (standardAugmentation A' (Under.mk φ') n))
          (ringOfMap (standardAugmentation A (Under.mk φ) n ≫ 𝟙 O))
          (standardTermRightHom_comp_augmentation (B := Under.mk φ) (B' := Under.mk φ')
            α (𝟙 O) hα n)).hom.app _)

/-- Degreewise map of simplicial cotangent modules induced by `inverseImageCommSqIso.inv`. -/
def etaleRestrictSimplicialHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n ⟶
      (simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g))).obj n :=
  baseChangeSimplicialHom (inverseImageCommSqIso p q g f sq).inv
    (compositeStructureMap p f) (structureMapLift g)
    (etaleRestrictTerm_w p q g f sq) n

/-- Degreewise reverse map of simplicial cotangent modules induced by
`inverseImageCommSqIso.hom`. -/
def etaleRestrictSimplicialInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g))).obj n ⟶
      (simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n :=
  baseChangeSimplicialHom (inverseImageCommSqIso p q g f sq).hom
    (structureMapLift g) (compositeStructureMap p f)
    (etaleRestrictTerm_w_hom p q g f sq) n

/-- Degreewise identification of simplicial cotangent modules of the composite algebra map
with those of `g^♯`. -/
def etaleRestrictSimplicialAppIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n ≅
      (simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g))).obj n where
  hom := etaleRestrictSimplicialHom p q g f sq n
  inv := etaleRestrictSimplicialInv p q g f sq n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Simplicial identification of cotangent modules of the composite algebra map with those
of `g^♯`. -/
def etaleRestrictSimplicialIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    simplicialModule (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) ≅
      simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g)) :=
  NatIso.ofComponents (etaleRestrictSimplicialAppIso p q g f sq) sorry

/-- Cochain-level identification `L(p⁻¹(f^♯) ≫ p^♯) ≅ L_{U/V}` induced by the étale
coefficient isomorphism. -/
def etaleRestrictCochainObjIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    cotangentCochainObj (compositeStructureMap p f) ≅ cotangentCochain g :=
  (embeddingDownNat.extendFunctor
      (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift U)))).mapIso
    ((alternatingFaceMapComplex
        (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift U)))).mapIso
      (etaleRestrictSimplicialIso p q g f sq))

/-- `etaleRestrictCochainObjIso` is `extendFunctor.mapIso` of the alternating-face image of
`etaleRestrictSimplicialIso`. -/
theorem etaleRestrictCochainObjIso_eq {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    etaleRestrictCochainObjIso p q g f sq =
      (embeddingDownNat.extendFunctor
          (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift U)))).mapIso
        ((alternatingFaceMapComplex
            (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift U)))).mapIso
          (etaleRestrictSimplicialIso p q g f sq)) :=
  sorry

/-- Cochain-level identification `Lp^* L_{X/Y} ≅ L_{U/V}` of an étale commutative square. -/
def etaleRestrictCochainIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    pullbackCotangentCochain p f ≅ cotangentCochain g :=
  asIso (transitivityMapCochain p f) ≪≫ etaleRestrictCochainObjIso p q g f sq

/-- `etaleRestrictCochainIso` is the étale transitivity isomorphism followed by the
composite-to-`L_{U/V}` identification. -/
theorem etaleRestrictCochainIso_eq {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    etaleRestrictCochainIso p q g f sq =
      asIso (transitivityMapCochain p f) ≪≫
        etaleRestrictCochainObjIso p q g f sq :=
  sorry

/-- Derived identification `Lp^* L_{X/Y} ≅ L_{U/V}` in `D(𝒪_U)` of an étale commutative
square. -/
def etaleRestrictIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    pullbackCotangent p f ≅ cotangent g :=
  DerivedCategory.Q.mapIso (etaleRestrictCochainIso p q g f sq)

/-- `etaleRestrictIso` is `DerivedCategory.Q.mapIso` of `etaleRestrictCochainIso`. -/
theorem etaleRestrictIso_eq {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f) :
    etaleRestrictIso p q g f sq =
      DerivedCategory.Q.mapIso (etaleRestrictCochainIso p q g f sq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
