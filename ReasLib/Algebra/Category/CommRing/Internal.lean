/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Internal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of internal commutative ring objects

This module refines the finite-product transport of internal ring objects to commutative ring
objects.  The carrier, additive structure, multiplication, and morphisms are inherited from
`Functor.mapRing`; only preservation of multiplicative commutativity is additional proof data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]

/-- The multiplicative monoid transported by a braided functor remains commutative. -/
theorem mapCommRing_isCommMonObj (R : CommRingObjCat C) :
    @IsCommMonObj D _ _ _ (F.obj R.X)
      (mapRingMonObj F ((CommRingObjCat.forget₂RingObjCat C).obj R)) := sorry

/-- The internal commutative-ring structure transported by a braided functor. -/
@[implicit_reducible]
noncomputable def mapCommRingObj (R : CommRingObjCat C) : CommRingObj (F.obj R.X) where
  toRingObj := mapRingObj F ((CommRingObjCat.forget₂RingObjCat C).obj R)
  toIsCommMonObj := mapCommRing_isCommMonObj F R

/-- The bundled internal commutative ring obtained by applying a braided functor. -/
noncomputable def mapCommRingObject (R : CommRingObjCat C) : CommRingObjCat D where
  X := F.obj R.X
  commRingObj := mapCommRingObj F R

/-- The internal commutative-ring morphism obtained by applying a braided functor. -/
noncomputable def mapCommRingMap {R S : CommRingObjCat C} (f : R ⟶ S) :
    mapCommRingObject F R ⟶ mapCommRingObject F S where
  hom := F.map f.hom
  isRingHom := mapRing_isRingHom F ((CommRingObjCat.forget₂RingObjCat C).map f)

/-- Mapping internal commutative rings preserves identity morphisms. -/
theorem mapCommRing_map_id (R : CommRingObjCat C) :
    mapCommRingMap F (𝟙 R) = 𝟙 (mapCommRingObject F R) := sorry

/-- Mapping internal commutative rings preserves composition of morphisms. -/
theorem mapCommRing_map_comp {R S T : CommRingObjCat C} (f : R ⟶ S) (g : S ⟶ T) :
    mapCommRingMap F (f ≫ g) = mapCommRingMap F f ≫ mapCommRingMap F g := sorry

/-- The functor on internal commutative rings induced by a braided monoidal functor. -/
noncomputable def mapCommRing : CommRingObjCat C ⥤ CommRingObjCat D where
  obj := mapCommRingObject F
  map := mapCommRingMap F
  map_id := mapCommRing_map_id F
  map_comp := mapCommRing_map_comp F

/-- Forgetting the transported commutative ring to the ambient category recovers the original
functor on carriers. -/
noncomputable def mapCommRingForgetIso :
    mapCommRing F ⋙ CommRingObjCat.forget D ≅ CommRingObjCat.forget C ⋙ F :=
  Iso.refl _

/-- Forgetting multiplicative commutativity after transport recovers transport of the underlying
internal ring. -/
noncomputable def mapCommRingForgetRingIso :
    mapCommRing F ⋙ CommRingObjCat.forget₂RingObjCat D ≅
      CommRingObjCat.forget₂RingObjCat C ⋙ mapRing F :=
  Iso.refl _

namespace MapCommRing

variable {F G : C ⥤ D} [F.Braided] [G.Braided]

/-- The component on an internal commutative ring of a lifted natural transformation. -/
noncomputable def natApp (alpha : F ⟶ G) (R : CommRingObjCat C) :
    mapCommRingObject F R ⟶ mapCommRingObject G R :=
  (CommRingObjCat.fullyFaithfulForget₂RingObjCat D).preimage
    (MapRing.natApp alpha ((CommRingObjCat.forget₂RingObjCat C).obj R))

/-- Lifted components are natural on internal commutative rings. -/
theorem natNaturality (alpha : F ⟶ G) {R S : CommRingObjCat C} (f : R ⟶ S) :
    (mapCommRing F).map f ≫ natApp alpha S =
      natApp alpha R ≫ (mapCommRing G).map f := sorry

end MapCommRing

/-- A natural transformation between braided functors lifts to internal commutative rings. -/
noncomputable def mapCommRingNatTrans {F G : C ⥤ D} [F.Braided] [G.Braided]
    (alpha : F ⟶ G) : mapCommRing F ⟶ mapCommRing G where
  app := MapCommRing.natApp alpha
  naturality := fun {R S} f ↦ MapCommRing.natNaturality alpha (R := R) (S := S) f

namespace MapCommRing

variable {F G : C ⥤ D} [F.Braided] [G.Braided]

/-- The two lifted directions of a natural isomorphism compose to the source identity. -/
theorem natIsoHomInvId (e : F ≅ G) :
    mapCommRingNatTrans e.hom ≫ mapCommRingNatTrans e.inv = 𝟙 (mapCommRing F) := sorry

/-- The two lifted directions of a natural isomorphism compose to the target identity. -/
theorem natIsoInvHomId (e : F ≅ G) :
    mapCommRingNatTrans e.inv ≫ mapCommRingNatTrans e.hom = 𝟙 (mapCommRing G) := sorry

end MapCommRing

/-- A natural isomorphism between braided functors lifts to internal commutative rings. -/
noncomputable def mapCommRingNatIso {F G : C ⥤ D} [F.Braided] [G.Braided] (e : F ≅ G) :
    mapCommRing F ≅ mapCommRing G where
  hom := mapCommRingNatTrans e.hom
  inv := mapCommRingNatTrans e.inv
  hom_inv_id := MapCommRing.natIsoHomInvId e
  inv_hom_id := MapCommRing.natIsoInvHomId e

namespace MapCommRing

/-- The component of the identity comparison, lifted through the fully faithful forgetful functor
to internal rings. -/
noncomputable def idAppIso (R : CommRingObjCat C) : mapCommRingObject (𝟭 C) R ≅ R :=
  (CommRingObjCat.fullyFaithfulForget₂RingObjCat C).preimageIso
    (MapRing.idAppIso ((CommRingObjCat.forget₂RingObjCat C).obj R))

/-- The identity comparison is natural in the internal commutative ring. -/
theorem idNaturality {R S : CommRingObjCat C} (f : R ⟶ S) :
    (mapCommRing (𝟭 C)).map f ≫ (idAppIso S).hom =
      (idAppIso R).hom ≫ (𝟭 (CommRingObjCat C)).map f := sorry

end MapCommRing

/-- Mapping internal commutative rings along the identity functor is naturally isomorphic to the
identity. -/
noncomputable def mapCommRingIdIso :
    mapCommRing (𝟭 C) ≅ 𝟭 (CommRingObjCat C) :=
  NatIso.ofComponents MapCommRing.idAppIso MapCommRing.idNaturality

namespace MapCommRing

variable {E : Type uE} [Category.{vE} E] [CartesianMonoidalCategory E] [BraidedCategory E]
variable (F : C ⥤ D) [F.Braided] (G : D ⥤ E) [G.Braided]

/-- The component comparing transport along a composite with successive transport. -/
noncomputable def compAppIso (R : CommRingObjCat C) :
    mapCommRingObject (F ⋙ G) R ≅ mapCommRingObject G (mapCommRingObject F R) :=
  (CommRingObjCat.fullyFaithfulForget₂RingObjCat E).preimageIso
    (MapRing.compAppIso F G ((CommRingObjCat.forget₂RingObjCat C).obj R))

/-- The composition comparison is natural in the internal commutative ring. -/
theorem compNaturality {R S : CommRingObjCat C} (f : R ⟶ S) :
    (mapCommRing (F ⋙ G)).map f ≫ (compAppIso F G S).hom =
      (compAppIso F G R).hom ≫ (mapCommRing F ⋙ mapCommRing G).map f := sorry

end MapCommRing

/-- Mapping internal commutative rings along a composite is naturally isomorphic to mapping
successively. -/
noncomputable def mapCommRingCompIso {E : Type uE} [Category.{vE} E]
    [CartesianMonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) [F.Braided] (G : D ⥤ E) [G.Braided] :
    mapCommRing (F ⋙ G) ≅ mapCommRing F ⋙ mapCommRing G :=
  NatIso.ofComponents (MapCommRing.compAppIso F G) (MapCommRing.compNaturality F G)

namespace MapCommRingAdjunction

variable {F : C ⥤ D} [F.Braided] {G : D ⥤ C} [G.Braided]

/-- The unit on internal commutative rings induced by an adjunction of braided functors. -/
noncomputable def unit (adj : F ⊣ G) :
    𝟭 (CommRingObjCat C) ⟶ mapCommRing F ⋙ mapCommRing G :=
  mapCommRingIdIso.inv ≫ mapCommRingNatTrans adj.unit ≫ (mapCommRingCompIso F G).hom

/-- The counit on internal commutative rings induced by an adjunction of braided functors. -/
noncomputable def counit (adj : F ⊣ G) :
    mapCommRing G ⋙ mapCommRing F ⟶ 𝟭 (CommRingObjCat D) :=
  (mapCommRingCompIso G F).inv ≫ mapCommRingNatTrans adj.counit ≫ mapCommRingIdIso.hom

/-- The left triangle identity for the induced unit and counit on internal commutative rings. -/
theorem leftTriangleComponents (adj : F ⊣ G) (R : CommRingObjCat C) :
    (mapCommRing F).map ((unit adj).app R) ≫
      (counit adj).app ((mapCommRing F).obj R) = 𝟙 ((mapCommRing F).obj R) := sorry

/-- The right triangle identity for the induced unit and counit on internal commutative rings. -/
theorem rightTriangleComponents (adj : F ⊣ G) (S : CommRingObjCat D) :
    (unit adj).app ((mapCommRing G).obj S) ≫
      (mapCommRing G).map ((counit adj).app S) = 𝟙 ((mapCommRing G).obj S) := sorry

end MapCommRingAdjunction

/-- An adjunction between braided functors lifts to their actions on internal commutative rings. -/
noncomputable def mapCommRingAdjunction {F : C ⥤ D} [F.Braided]
    {G : D ⥤ C} [G.Braided] (adj : F ⊣ G) : mapCommRing F ⊣ mapCommRing G where
  unit := MapCommRingAdjunction.unit adj
  counit := MapCommRingAdjunction.counit adj
  left_triangle_components := MapCommRingAdjunction.leftTriangleComponents adj
  right_triangle_components := MapCommRingAdjunction.rightTriangleComponents adj

/-- Changing the proof-irrelevant braided structure on a fixed functor changes the commutative-ring
lift only by the canonical identity-on-carriers isomorphism. -/
noncomputable def mapCommRingBraidedIso (F : C ⥤ D) (b₁ b₂ : F.Braided) :
    @mapCommRing C _ _ _ D _ _ _ F b₁ ≅ @mapCommRing C _ _ _ D _ _ _ F b₂ :=
  @mapCommRingNatIso C _ _ _ D _ _ _ F F b₁ b₂ (Iso.refl F)

/-- The canonical functor on internal commutative rings induced by a finite-product-preserving
functor. -/
@[stacks 0FRE "finite-product transport of internal commutative rings"]
noncomputable def mapCommRingOfFiniteProducts (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] : CommRingObjCat C ⥤ CommRingObjCat D :=
  @mapCommRing C _ _ _ D _ _ _ F (Braided.ofChosenFiniteProducts F)

/-- Forgetting the finite-product transport of internal commutative rings recovers the original
functor on carriers. -/
@[stacks 0FRE "carrier comparison for internal commutative-ring transport"]
noncomputable def mapCommRingOfFiniteProductsForgetIso (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] :
    mapCommRingOfFiniteProducts F ⋙ CommRingObjCat.forget D ≅
      CommRingObjCat.forget C ⋙ F :=
  Iso.refl _

/-- Forgetting commutativity after finite-product transport agrees with transporting the underlying
internal ring. -/
@[stacks 0FRE "underlying ring comparison for internal commutative-ring transport"]
noncomputable def mapCommRingOfFiniteProductsForgetRingIso (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] :
    mapCommRingOfFiniteProducts F ⋙ CommRingObjCat.forget₂RingObjCat D ≅
      CommRingObjCat.forget₂RingObjCat C ⋙ mapRingOfFiniteProducts F :=
  Iso.refl _

/-- A natural transformation between finite-product-preserving functors lifts canonically to
internal commutative rings. -/
noncomputable def mapCommRingOfFiniteProductsNatTrans {F G : C ⥤ D}
    [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G] (alpha : F ⟶ G) :
    mapCommRingOfFiniteProducts F ⟶ mapCommRingOfFiniteProducts G :=
  @mapCommRingNatTrans C _ _ _ D _ _ _ F G
    (Braided.ofChosenFiniteProducts F) (Braided.ofChosenFiniteProducts G) alpha

/-- A natural isomorphism between finite-product-preserving functors lifts canonically to internal
commutative rings. -/
noncomputable def mapCommRingOfFiniteProductsNatIso {F G : C ⥤ D}
    [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G] (e : F ≅ G) :
    mapCommRingOfFiniteProducts F ≅ mapCommRingOfFiniteProducts G :=
  @mapCommRingNatIso C _ _ _ D _ _ _ F G
    (Braided.ofChosenFiniteProducts F) (Braided.ofChosenFiniteProducts G) e

/-- An adjunction between finite-product-preserving functors induces an adjunction on internal
commutative rings. -/
@[stacks 0FRE "adjunction on internal commutative rings"]
noncomputable def mapCommRingOfFiniteProductsAdjunction {F : C ⥤ D}
    [Limits.PreservesFiniteProducts F] {G : D ⥤ C}
    [Limits.PreservesFiniteProducts G] (adj : F ⊣ G) :
    mapCommRingOfFiniteProducts F ⊣ mapCommRingOfFiniteProducts G :=
  @mapCommRingAdjunction C _ _ _ D _ _ _ F
    (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G) adj

/-- The finite-product transport along the identity is canonically isomorphic to the identity on
internal commutative rings. -/
noncomputable def mapCommRingOfFiniteProductsIdIso :
    mapCommRingOfFiniteProducts (𝟭 C) ≅ 𝟭 (CommRingObjCat C) :=
  mapCommRingBraidedIso (𝟭 C) (Braided.ofChosenFiniteProducts (𝟭 C)) inferInstance ≪≫
    mapCommRingIdIso

/-- Finite-product transport along a composite agrees with successive transport on internal
commutative rings. -/
noncomputable def mapCommRingOfFiniteProductsCompIso {E : Type uE} [Category.{vE} E]
    [CartesianMonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) [Limits.PreservesFiniteProducts F]
    (G : D ⥤ E) [Limits.PreservesFiniteProducts G] :
    mapCommRingOfFiniteProducts (F ⋙ G) ≅
      mapCommRingOfFiniteProducts F ⋙ mapCommRingOfFiniteProducts G :=
  mapCommRingBraidedIso (F ⋙ G) (Braided.ofChosenFiniteProducts (F ⋙ G))
      (@compositeBraided C _ _ _ D _ _ _ E _ _ _ F
        (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G)) ≪≫
    @mapCommRingCompIso C _ _ _ D _ _ _ E _ _ _ F
      (Braided.ofChosenFiniteProducts F) G (Braided.ofChosenFiniteProducts G)

/- The `sorryAx` in these data owners is confined to commutativity, naturality, and adjunction-law
proof fields; their carriers, operations, functors, transformations, and isomorphism maps are
explicitly inherited from `mapRing`. -/

end CategoryTheory.Functor
