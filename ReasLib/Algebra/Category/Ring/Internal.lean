module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Functoriality of internal ring objects

This module lifts braided monoidal functors between cartesian monoidal categories to their
categories of internal ring objects.  In particular, every finite-product-preserving functor
acts canonically on internal rings once equipped with the canonical cartesian monoidal data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.AddMonObj CategoryTheory.MonObj

noncomputable section

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]

/-- The additive-group structure on the image of an internal ring. -/
noncomputable abbrev mapRingAddGrpObj (R : RingObjCat C) : AddGrpObj (F.obj R.X) :=
  (F.mapAddGrp.obj ⟨R.X⟩).addGrp

/-- The multiplicative-monoid structure on the image of an internal ring. -/
noncomputable abbrev mapRingMonObj (R : RingObjCat C) : MonObj (F.obj R.X) :=
  (F.mapMon.obj ⟨R.X⟩).mon

/-- The addition on the image of an internal ring. -/
noncomputable abbrev mapRingAdd (R : RingObjCat C) :
    F.obj R.X ⊗ F.obj R.X ⟶ F.obj R.X :=
  @AddMonObj.add D _ _ _ (mapRingAddGrpObj F R).toAddMonObj

/-- The multiplication on the image of an internal ring. -/
noncomputable abbrev mapRingMul (R : RingObjCat C) :
    F.obj R.X ⊗ F.obj R.X ⟶ F.obj R.X :=
  @MonObj.mul D _ _ _ (mapRingMonObj F R)

/-- The image additive law remains commutative. -/
theorem mapRing_isCommAddMonObj (R : RingObjCat C) :
    @IsCommAddMonObj D _ _ _ (F.obj R.X) (mapRingAddGrpObj F R).toAddMonObj := sorry

/-- A braided monoidal functor preserves the left distributivity law of an internal ring. -/
theorem mapRing_mul_add (R : RingObjCat C) :
    F.obj R.X ◁ mapRingAdd F R ≫ mapRingMul F R =
      lift ((F.obj R.X ◁ fst _ _) ≫ mapRingMul F R)
          ((F.obj R.X ◁ snd _ _) ≫ mapRingMul F R) ≫
        mapRingAdd F R := sorry

/-- A braided monoidal functor preserves the right distributivity law of an internal ring. -/
theorem mapRing_add_mul (R : RingObjCat C) :
    mapRingAdd F R ▷ F.obj R.X ≫ mapRingMul F R =
      lift (fst _ _ ▷ F.obj R.X ≫ mapRingMul F R)
          (snd _ _ ▷ F.obj R.X ≫ mapRingMul F R) ≫
        mapRingAdd F R := sorry

/-- The internal ring structure carried by the image of an internal ring under a braided
monoidal functor. -/
@[implicit_reducible]
noncomputable def mapRingObj (R : RingObjCat C) : RingObj (F.obj R.X) where
  toAddGrpObj := mapRingAddGrpObj F R
  toIsCommAddMonObj := mapRing_isCommAddMonObj F R
  toMonObj := mapRingMonObj F R
  mul_add := mapRing_mul_add F R
  add_mul := mapRing_add_mul F R

/-- A braided monoidal functor takes morphisms of internal rings to morphisms of internal
rings. -/
theorem mapRing_isRingHom {R S : RingObjCat C} (f : R ⟶ S) :
    @IsRingHom D _ _ (F.obj R.X) (F.obj S.X)
      (mapRingAddGrpObj F R).toAddMonObj (mapRingAddGrpObj F S).toAddMonObj
      (mapRingMonObj F R) (mapRingMonObj F S) (F.map f.hom) := sorry

/-- The internal ring object obtained by applying a braided monoidal functor. -/
noncomputable def mapRingObject (R : RingObjCat C) : RingObjCat D where
  X := F.obj R.X
  ringObj := mapRingObj F R

/-- The internal-ring morphism obtained by applying a braided monoidal functor. -/
noncomputable def mapRingMap {R S : RingObjCat C} (f : R ⟶ S) :
    mapRingObject F R ⟶ mapRingObject F S where
  hom := F.map f.hom
  isRingHom := mapRing_isRingHom F f

/-- Mapping internal rings preserves identity morphisms. -/
theorem mapRing_map_id (R : RingObjCat C) :
    mapRingMap F (𝟙 R) = 𝟙 (mapRingObject F R) := sorry

/-- Mapping internal rings preserves composition of morphisms. -/
theorem mapRing_map_comp {R S T : RingObjCat C} (f : R ⟶ S) (g : S ⟶ T) :
    mapRingMap F (f ≫ g) = mapRingMap F f ≫ mapRingMap F g := sorry

/-- The functor on internal rings induced by a braided monoidal functor. -/
noncomputable def mapRing : RingObjCat C ⥤ RingObjCat D where
  obj := mapRingObject F
  map := mapRingMap F
  map_id := mapRing_map_id F
  map_comp := mapRing_map_comp F

/-- Forgetting the internal ring structure after `mapRing` recovers the original functor on
underlying objects. -/
noncomputable def mapRingForgetIso :
    mapRing F ⋙ RingObjCat.forget D ≅ RingObjCat.forget C ⋙ F :=
  Iso.refl _

namespace MapRing

variable {F G : C ⥤ D} [F.Braided] [G.Braided]

/-- A component of a natural transformation between braided monoidal functors preserves the
internal-ring operations. -/
theorem natAppIsRingHom (α : F ⟶ G) (R : RingObjCat C) :
    @IsRingHom D _ _ (F.obj R.X) (G.obj R.X)
      (mapRingAddGrpObj F R).toAddMonObj (mapRingAddGrpObj G R).toAddMonObj
      (mapRingMonObj F R) (mapRingMonObj G R) (α.app R.X) := sorry

/-- The component on an internal ring of the lift of a monoidal natural transformation. -/
noncomputable def natApp (α : F ⟶ G) (R : RingObjCat C) :
    mapRingObject F R ⟶ mapRingObject G R where
  hom := α.app R.X
  isRingHom := natAppIsRingHom α R

/-- The lifted components of a natural transformation are natural on internal rings. -/
theorem natNaturality (α : F ⟶ G) {R S : RingObjCat C} (f : R ⟶ S) :
    (mapRing F).map f ≫ natApp α S = natApp α R ≫ (mapRing G).map f := sorry

end MapRing

/-- A natural transformation between braided monoidal functors lifts to internal rings. -/
noncomputable def mapRingNatTrans {F G : C ⥤ D} [F.Braided] [G.Braided] (α : F ⟶ G) :
    mapRing F ⟶ mapRing G where
  app := MapRing.natApp α
  naturality := fun {R S} f ↦ MapRing.natNaturality α (R := R) (S := S) f

namespace MapRing

variable {F G : C ⥤ D} [F.Braided] [G.Braided]

/-- The lifted natural transformations associated to the two directions of a natural
isomorphism compose to the identity on its source. -/
theorem natIsoHomInvId (e : F ≅ G) :
    mapRingNatTrans e.hom ≫ mapRingNatTrans e.inv = 𝟙 (mapRing F) := sorry

/-- The lifted natural transformations associated to the two directions of a natural
isomorphism compose to the identity on its target. -/
theorem natIsoInvHomId (e : F ≅ G) :
    mapRingNatTrans e.inv ≫ mapRingNatTrans e.hom = 𝟙 (mapRing G) := sorry

end MapRing

/-- A natural isomorphism between braided monoidal functors lifts to internal rings. -/
noncomputable def mapRingNatIso {F G : C ⥤ D} [F.Braided] [G.Braided] (e : F ≅ G) :
    mapRing F ≅ mapRing G where
  hom := mapRingNatTrans e.hom
  inv := mapRingNatTrans e.inv
  hom_inv_id := MapRing.natIsoHomInvId e
  inv_hom_id := MapRing.natIsoInvHomId e

namespace MapRingAdjunction

variable {F : C ⥤ D} [F.Braided] {G : D ⥤ C} [G.Braided]
variable (adj : F ⊣ G)

/-- The adjunct of an internal-ring morphism is again an internal-ring morphism. -/
theorem homIsRingHom {R : RingObjCat C} {S : RingObjCat D}
    (h : mapRingObject F R ⟶ S) :
    @IsRingHom C _ _ R.X (G.obj S.X)
      R.ringObj.toAddGrpObj.toAddMonObj (mapRingAddGrpObj G S).toAddMonObj
      R.ringObj.toMonObj (mapRingMonObj G S)
      (adj.homEquiv R.X S.X h.hom) := sorry

/-- Apply the underlying adjunction to an internal-ring morphism. -/
noncomputable def hom {R : RingObjCat C} {S : RingObjCat D}
    (h : mapRingObject F R ⟶ S) : R ⟶ mapRingObject G S where
  hom := adj.homEquiv R.X S.X h.hom
  isRingHom := homIsRingHom adj h

/-- The inverse adjunct of an internal-ring morphism is again an internal-ring morphism. -/
theorem invIsRingHom {R : RingObjCat C} {S : RingObjCat D}
    (h : R ⟶ mapRingObject G S) :
    @IsRingHom D _ _ (F.obj R.X) S.X
      (mapRingAddGrpObj F R).toAddMonObj S.ringObj.toAddGrpObj.toAddMonObj
      (mapRingMonObj F R) S.ringObj.toMonObj
      ((adj.homEquiv R.X S.X).symm h.hom) := sorry

/-- Apply the inverse underlying adjunction to an internal-ring morphism. -/
noncomputable def inv {R : RingObjCat C} {S : RingObjCat D}
    (h : R ⟶ mapRingObject G S) : mapRingObject F R ⟶ S where
  hom := (adj.homEquiv R.X S.X).symm h.hom
  isRingHom := invIsRingHom adj h

/-- Taking an adjunct and then its inverse recovers the original internal-ring morphism. -/
theorem leftInv {R : RingObjCat C} {S : RingObjCat D}
    (h : mapRingObject F R ⟶ S) : inv adj (hom adj h) = h := sorry

/-- Taking an inverse adjunct and then its adjunct recovers the original internal-ring
morphism. -/
theorem rightInv {R : RingObjCat C} {S : RingObjCat D}
    (h : R ⟶ mapRingObject G S) : hom adj (inv adj h) = h := sorry

/-- The hom-set equivalence on internal rings induced by an adjunction of braided functors. -/
noncomputable def homEquiv (R : RingObjCat C) (S : RingObjCat D) :
    (mapRingObject F R ⟶ S) ≃ (R ⟶ mapRingObject G S) where
  toFun := hom adj
  invFun := inv adj
  left_inv := leftInv adj
  right_inv := rightInv adj

/-- The internal-ring hom-set equivalence is natural in its source. -/
theorem naturalityLeftSymm {R' R : RingObjCat C} {S : RingObjCat D}
    (f : R' ⟶ R) (g : R ⟶ mapRingObject G S) :
    inv adj (f ≫ g) = mapRingMap F f ≫ inv adj g := sorry

/-- The internal-ring hom-set equivalence is natural in its target. -/
theorem naturalityRight {R : RingObjCat C} {S S' : RingObjCat D}
    (f : mapRingObject F R ⟶ S) (g : S ⟶ S') :
    hom adj (f ≫ g) = hom adj f ≫ mapRingMap G g := sorry

end MapRingAdjunction

/-- An adjunction between braided functors induces an adjunction on internal rings. -/
noncomputable def mapRingAdjunction {F : C ⥤ D} [F.Braided]
    {G : D ⥤ C} [G.Braided] (adj : F ⊣ G) : mapRing F ⊣ mapRing G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := MapRingAdjunction.homEquiv adj
      homEquiv_naturality_left_symm := MapRingAdjunction.naturalityLeftSymm adj
      homEquiv_naturality_right := MapRingAdjunction.naturalityRight adj }

namespace MapRing

/-- The identity on the underlying object is an internal-ring morphism from the image under the
identity functor. -/
theorem idHomIsRingHom (R : RingObjCat C) :
    @IsRingHom C _ _ ((𝟭 C).obj R.X) R.X
      (mapRingAddGrpObj (𝟭 C) R).toAddMonObj R.ringObj.toAddGrpObj.toAddMonObj
      (mapRingMonObj (𝟭 C) R) R.ringObj.toMonObj (𝟙 R.X) := sorry

/-- The forward component of the identity comparison for mapped internal rings. -/
noncomputable def idHom (R : RingObjCat C) : mapRingObject (𝟭 C) R ⟶ R where
  hom := 𝟙 R.X
  isRingHom := idHomIsRingHom R

/-- The identity on the underlying object is an internal-ring morphism into the image under the
identity functor. -/
theorem idInvIsRingHom (R : RingObjCat C) :
    @IsRingHom C _ _ R.X ((𝟭 C).obj R.X)
      R.ringObj.toAddGrpObj.toAddMonObj (mapRingAddGrpObj (𝟭 C) R).toAddMonObj
      R.ringObj.toMonObj (mapRingMonObj (𝟭 C) R) (𝟙 R.X) := sorry

/-- The inverse component of the identity comparison for mapped internal rings. -/
noncomputable def idInv (R : RingObjCat C) : R ⟶ mapRingObject (𝟭 C) R where
  hom := 𝟙 R.X
  isRingHom := idInvIsRingHom R

/-- The two component maps of the identity comparison compose to the source identity. -/
theorem idHomInvId (R : RingObjCat C) :
    idHom R ≫ idInv R = 𝟙 (mapRingObject (𝟭 C) R) := sorry

/-- The two component maps of the identity comparison compose to the target identity. -/
theorem idInvHomId (R : RingObjCat C) : idInv R ≫ idHom R = 𝟙 R := sorry

/-- The component of the identity comparison for the functor on internal rings. -/
noncomputable def idAppIso (R : RingObjCat C) : mapRingObject (𝟭 C) R ≅ R where
  hom := idHom R
  inv := idInv R
  hom_inv_id := idHomInvId R
  inv_hom_id := idInvHomId R

/-- The components of the identity comparison are natural in the internal ring. -/
theorem idNaturality {R S : RingObjCat C} (f : R ⟶ S) :
    (mapRing (𝟭 C)).map f ≫ (idAppIso S).hom =
      (idAppIso R).hom ≫ (𝟭 (RingObjCat C)).map f := sorry

end MapRing

/-- Mapping internal rings along the identity functor is naturally isomorphic to the identity. -/
noncomputable def mapRingIdIso : mapRing (𝟭 C) ≅ 𝟭 (RingObjCat C) :=
  NatIso.ofComponents MapRing.idAppIso MapRing.idNaturality

namespace MapRing

variable {E : Type uE} [Category.{vE} E] [CartesianMonoidalCategory E] [BraidedCategory E]
variable (F : C ⥤ D) [F.Braided] (G : D ⥤ E) [G.Braided]

/-- The identity on the underlying object is an internal-ring morphism from mapping along a
composite to mapping successively. -/
theorem compHomIsRingHom (R : RingObjCat C) :
    @IsRingHom E _ _ ((F ⋙ G).obj R.X) (G.obj (F.obj R.X))
      (mapRingAddGrpObj (F ⋙ G) R).toAddMonObj
      (mapRingAddGrpObj G (mapRingObject F R)).toAddMonObj
      (mapRingMonObj (F ⋙ G) R) (mapRingMonObj G (mapRingObject F R))
      (𝟙 (G.obj (F.obj R.X))) := sorry

/-- The forward component of the composition comparison for mapped internal rings. -/
noncomputable def compHom (R : RingObjCat C) :
    mapRingObject (F ⋙ G) R ⟶ mapRingObject G (mapRingObject F R) where
  hom := 𝟙 (G.obj (F.obj R.X))
  isRingHom := compHomIsRingHom F G R

/-- The identity on the underlying object is an internal-ring morphism from successive mapping
to mapping along a composite. -/
theorem compInvIsRingHom (R : RingObjCat C) :
    @IsRingHom E _ _ (G.obj (F.obj R.X)) ((F ⋙ G).obj R.X)
      (mapRingAddGrpObj G (mapRingObject F R)).toAddMonObj
      (mapRingAddGrpObj (F ⋙ G) R).toAddMonObj
      (mapRingMonObj G (mapRingObject F R)) (mapRingMonObj (F ⋙ G) R)
      (𝟙 (G.obj (F.obj R.X))) := sorry

/-- The inverse component of the composition comparison for mapped internal rings. -/
noncomputable def compInv (R : RingObjCat C) :
    mapRingObject G (mapRingObject F R) ⟶ mapRingObject (F ⋙ G) R where
  hom := 𝟙 (G.obj (F.obj R.X))
  isRingHom := compInvIsRingHom F G R

/-- The two component maps of the composition comparison compose to the source identity. -/
theorem compHomInvId (R : RingObjCat C) :
    compHom F G R ≫ compInv F G R = 𝟙 (mapRingObject (F ⋙ G) R) := sorry

/-- The two component maps of the composition comparison compose to the target identity. -/
theorem compInvHomId (R : RingObjCat C) :
    compInv F G R ≫ compHom F G R = 𝟙 (mapRingObject G (mapRingObject F R)) := sorry

/-- The component of the comparison between mapping along a composite and mapping successively. -/
noncomputable def compAppIso (R : RingObjCat C) :
    mapRingObject (F ⋙ G) R ≅ mapRingObject G (mapRingObject F R) where
  hom := compHom F G R
  inv := compInv F G R
  hom_inv_id := compHomInvId F G R
  inv_hom_id := compInvHomId F G R

/-- The components of the composition comparison are natural in the internal ring. -/
theorem compNaturality {R S : RingObjCat C} (f : R ⟶ S) :
    (mapRing (F ⋙ G)).map f ≫ (compAppIso F G S).hom =
      (compAppIso F G R).hom ≫ (mapRing F ⋙ mapRing G).map f := sorry

end MapRing

/-- Mapping internal rings along a composite is naturally isomorphic to mapping successively. -/
noncomputable def mapRingCompIso {E : Type uE} [Category.{vE} E]
    [CartesianMonoidalCategory E] [BraidedCategory E] (F : C ⥤ D) [F.Braided]
    (G : D ⥤ E) [G.Braided] : mapRing (F ⋙ G) ≅ mapRing F ⋙ mapRing G :=
  NatIso.ofComponents (MapRing.compAppIso F G) (MapRing.compNaturality F G)

/-- The canonical functor on internal rings induced by a finite-product-preserving functor.
The canonical braided structure is supplied explicitly, so callers need no local instance. -/
noncomputable def mapRingOfFiniteProducts (F : C ⥤ D) [Limits.PreservesFiniteProducts F] :
    RingObjCat C ⥤ RingObjCat D :=
  @mapRing C _ _ _ D _ _ _ F (Braided.ofChosenFiniteProducts F)

/-- Forgetting internal rings after the canonical finite-product lift recovers the original
functor on underlying objects. -/
noncomputable def mapRingOfFiniteProductsForgetIso (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] :
    mapRingOfFiniteProducts F ⋙ RingObjCat.forget D ≅ RingObjCat.forget C ⋙ F :=
  Iso.refl _

/-- Changing the proof-irrelevant braided structure on a fixed functor does not change its
lift to internal rings, up to the canonical identity-on-carriers isomorphism. -/
noncomputable def mapRingBraidedIso (F : C ⥤ D) (b₁ b₂ : F.Braided) :
    @mapRing C _ _ _ D _ _ _ F b₁ ≅ @mapRing C _ _ _ D _ _ _ F b₂ :=
  @mapRingNatIso C _ _ _ D _ _ _ F F b₁ b₂ (Iso.refl F)

/-- A natural transformation between finite-product-preserving functors lifts canonically to
their actions on internal rings. -/
noncomputable def mapRingOfFiniteProductsNatTrans {F G : C ⥤ D}
    [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G] (α : F ⟶ G) :
    mapRingOfFiniteProducts F ⟶ mapRingOfFiniteProducts G :=
  @mapRingNatTrans C _ _ _ D _ _ _ F G
    (Braided.ofChosenFiniteProducts F) (Braided.ofChosenFiniteProducts G) α

/-- A natural isomorphism between finite-product-preserving functors lifts canonically to
their actions on internal rings. -/
noncomputable def mapRingOfFiniteProductsNatIso {F G : C ⥤ D}
    [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G] (e : F ≅ G) :
    mapRingOfFiniteProducts F ≅ mapRingOfFiniteProducts G :=
  @mapRingNatIso C _ _ _ D _ _ _ F G
    (Braided.ofChosenFiniteProducts F) (Braided.ofChosenFiniteProducts G) e

/-- An adjunction between finite-product-preserving functors induces an adjunction on their
canonical actions on internal rings. -/
noncomputable def mapRingOfFiniteProductsAdjunction {F : C ⥤ D}
    [Limits.PreservesFiniteProducts F] {G : D ⥤ C}
    [Limits.PreservesFiniteProducts G] (adj : F ⊣ G) :
    mapRingOfFiniteProducts F ⊣ mapRingOfFiniteProducts G :=
  @mapRingAdjunction C _ _ _ D _ _ _ F
    (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G) adj

/-- The canonical braided structure on a composite, named so that comparison APIs can pass
the structures of the two factors explicitly without installing local instances. -/
noncomputable abbrev compositeBraided {E : Type uE} [Category.{vE} E]
    [CartesianMonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ E) [G.Braided] : (F ⋙ G).Braided :=
  inferInstance

/-- Mapping internal rings along the identity by the canonical finite-product lift is
naturally isomorphic to the identity functor. -/
noncomputable def mapRingOfFiniteProductsIdIso :
    mapRingOfFiniteProducts (𝟭 C) ≅ 𝟭 (RingObjCat C) :=
  mapRingBraidedIso (𝟭 C) (Braided.ofChosenFiniteProducts (𝟭 C)) inferInstance ≪≫
    mapRingIdIso

/-- The canonical finite-product lift along a composite agrees with successive lifts on
internal rings. -/
noncomputable def mapRingOfFiniteProductsCompIso {E : Type uE} [Category.{vE} E]
    [CartesianMonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) [Limits.PreservesFiniteProducts F]
    (G : D ⥤ E) [Limits.PreservesFiniteProducts G] :
    mapRingOfFiniteProducts (F ⋙ G) ≅
      mapRingOfFiniteProducts F ⋙ mapRingOfFiniteProducts G :=
  mapRingBraidedIso (F ⋙ G) (Braided.ofChosenFiniteProducts (F ⋙ G))
      (@compositeBraided C _ _ _ D _ _ _ E _ _ _ F
        (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G)) ≪≫
    @mapRingCompIso C _ _ _ D _ _ _ E _ _ _ F
      (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G)

end CategoryTheory.Functor
