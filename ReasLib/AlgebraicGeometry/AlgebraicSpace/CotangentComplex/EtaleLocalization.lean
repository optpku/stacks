module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtalePullback

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

-- The public coefficient comparison uses a private inverse-image implementation.
set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable {S : Scheme.{u}}

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

/-- Lifting the forward and inverse maps of a sheaf isomorphism preserves their
forward-inverse identity. -/
theorem liftSheafIso_hom_inv_id (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    liftSheafMap X e.hom ≫ liftSheafMap X e.inv = 𝟙 (liftSheafObj X R) :=
  sorry

/-- Lifting the inverse and forward maps of a sheaf isomorphism preserves their
inverse-forward identity. -/
theorem liftSheafIso_inv_hom_id (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    liftSheafMap X e.inv ≫ liftSheafMap X e.hom = 𝟙 (liftSheafObj X R') :=
  sorry

/-- Universe lift of an isomorphism of commutative-ring sheaves on the small étale site. -/
def liftSheafIso (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    liftSheafObj X R ≅ liftSheafObj X R' where
  hom := liftSheafMap X e.hom
  inv := liftSheafMap X e.inv
  hom_inv_id := liftSheafIso_hom_inv_id X e
  inv_hom_id := liftSheafIso_inv_hom_id X e

/-- The underlying maps of `liftSheafIso` are `liftSheafMap` of the unlifted iso. -/
theorem liftSheafIso_hom (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (e : R ≅ R') :
    (liftSheafIso X e).hom = liftSheafMap X e.hom :=
  rfl

/-- Inverse image of an isomorphism of commutative-ring sheaves. -/
private def commSheafInverseImageMapIso {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (e : R ≅ R') :
    commSheafInverseImageObj h R ≅ commSheafInverseImageObj h R' :=
  (CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u} ⋙
    internalCommRingInverseImage h ⋙
    CategoryTheory.Sheaf.InternalCommRing.fromInternal.{u + 1, u, u}).mapIso e

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
    AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageCompIso
      g q (commStructureSheaf Y) ≪≫
    eqToIso (congrArg
      (fun h : U ⟶ Y ↦ commSheafInverseImageObj h (commStructureSheaf Y)) sq.w) ≪≫
    (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageCompIso
      p f (commStructureSheaf Y)).symm

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
    (by simpa only [Category.comp_id] using compositeStructureMap_eq_inv p q g f sq) n

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
    (by simpa only [Category.comp_id] using compositeStructureMap_eq p q g f sq) n

/-- The forward and reverse degreewise étale comparisons compose to the identity. -/
theorem etaleRestrictSimplicialAppIso_hom_inv_id {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) (n : SimplexCategoryᵒᵖ) :
    etaleRestrictSimplicialHom p q g f sq n ≫ etaleRestrictSimplicialInv p q g f sq n =
      𝟙 ((simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n) :=
  sorry

/-- The reverse and forward degreewise étale comparisons compose to the identity. -/
theorem etaleRestrictSimplicialAppIso_inv_hom_id {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) (n : SimplexCategoryᵒᵖ) :
    etaleRestrictSimplicialInv p q g f sq n ≫ etaleRestrictSimplicialHom p q g f sq n =
      𝟙 ((simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g))).obj n) :=
  sorry

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
  hom_inv_id := etaleRestrictSimplicialAppIso_hom_inv_id p q g f sq n
  inv_hom_id := etaleRestrictSimplicialAppIso_inv_hom_id p q g f sq n

/-- The degreewise étale comparisons commute with all simplicial operators. -/
theorem etaleRestrictSimplicialIso_naturality {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f)
    {m n : SimplexCategoryᵒᵖ} (a : m ⟶ n) :
    (simplicialModule (pulledInverseImage p f) (Under.mk (compositeStructureMap p f))).map a ≫
        (etaleRestrictSimplicialAppIso p q g f sq n).hom =
      (etaleRestrictSimplicialAppIso p q g f sq m).hom ≫
        (simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g))).map a :=
  sorry

/-- Simplicial identification of cotangent modules of the composite algebra map with those
of `g^♯`. -/
def etaleRestrictSimplicialIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale q] (sq : CommSq g p q f) :
    simplicialModule (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) ≅
      simplicialModule (inverseImageLift g) (Under.mk (structureMapLift g)) :=
  NatIso.ofComponents (etaleRestrictSimplicialAppIso p q g f sq)
    (etaleRestrictSimplicialIso_naturality p q g f sq)

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
