/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.Ring.Sheaf.Internal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutative-ring-valued sheaves as internal commutative rings

This module refines the equivalence between ring-valued sheaves and internal ring objects along the
fully faithful forgetful functors from commutative rings.  The only additional mathematical datum is
sectionwise multiplicative commutativity; all carriers, operations, restriction maps, functors, and
comparison isomorphisms are inherited explicitly from the internal-ring equivalence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.InternalCommRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Internal commutative-ring objects in type-valued sheaves, using the canonical cartesian
braiding fixed by `InternalRing.sheafBraidedCategory`. -/
abbrev CommRingObjects (J : GrothendieckTopology C) :=
  @CommRingObjCat (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)

namespace CommRingObjects

/-- The underlying type-valued sheaf of an internal commutative ring. -/
abbrev carrier (J : GrothendieckTopology C) (R : CommRingObjects J) : Sheaf J (Type w) :=
  @CommRingObjCat.X (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J) R

/-- The internal commutative-ring structure on an object of `CommRingObjects J`. -/
abbrev commRingObj (J : GrothendieckTopology C) (R : CommRingObjects J) :
    @CommRingObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J) (carrier J R) :=
  @CommRingObjCat.commRingObj (Sheaf J (Type w)) _ _
    (InternalRing.sheafBraidedCategory J) R

/-- Morphisms between internal commutative rings with the canonical sheaf braiding fixed. -/
abbrev Hom (J : GrothendieckTopology C) (R S : CommRingObjects J) :=
  @CommRingObjCat.Hom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J) R S

/-- The underlying morphism of type-valued sheaves of an internal commutative-ring morphism. -/
abbrev hom (J : GrothendieckTopology C) {R S : CommRingObjects J} (f : Hom J R S) :
    carrier J R ⟶ carrier J S :=
  @CommRingObjCat.Hom.hom (Sheaf J (Type w)) _ _
    (InternalRing.sheafBraidedCategory J) R S f

/-- The category structure on internal commutative rings with the canonical sheaf braiding fixed. -/
noncomputable instance (priority := high) category (J : GrothendieckTopology C) :
    Category (CommRingObjects J) :=
  @CommRingObjCat.instCategory (Sheaf J (Type w)) _ _
    (InternalRing.sheafBraidedCategory J)

/-- Forget an internal commutative ring to its underlying type-valued sheaf. -/
def forget (J : GrothendieckTopology C) : CommRingObjects J ⥤ Sheaf J (Type w) :=
  @CommRingObjCat.forget (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)

/-- Forget multiplicative commutativity from an internal commutative ring. -/
def forgetRing (J : GrothendieckTopology C) :
    CommRingObjects J ⥤ InternalRing.RingObjects J :=
  @CommRingObjCat.forget₂RingObjCat (Sheaf J (Type w)) _ _
    (InternalRing.sheafBraidedCategory J)

/-- Forgetting multiplicative commutativity from internal commutative rings is fully faithful. -/
def fullyFaithfulForgetRing (J : GrothendieckTopology C) : (forgetRing J).FullyFaithful :=
  @CommRingObjCat.fullyFaithfulForget₂RingObjCat (Sheaf J (Type w)) _ _
    (InternalRing.sheafBraidedCategory J)

/-- Composition of morphisms between internal commutative rings. -/
def comp (J : GrothendieckTopology C) {R S T : CommRingObjects J}
    (f : Hom J R S) (g : Hom J S T) : Hom J R T :=
  @CategoryStruct.comp (CommRingObjects J)
    (@Category.toCategoryStruct (CommRingObjects J) (category J)) R S T f g

end CommRingObjects

namespace CommRingSheaves

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Forget multiplicative commutativity from a commutative-ring-valued sheaf. -/
def forgetRing : Sheaf J CommRingCat.{w} ⥤ Sheaf J RingCat.{w} :=
  sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})

/-- The sheaf-level functor forgetting multiplicative commutativity is fully faithful, with its
preimage operation inherited explicitly from the coefficient-level forgetful functor. -/
def fullyFaithfulForgetRing : (forgetRing (J := J)).FullyFaithful :=
  fullyFaithfulSheafCompose J CommRingCat.fullyFaithfulForget₂ToRingCat

end CommRingSheaves

section ToInternal

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget RingCat.{w})]

namespace ToInternal

/-- The ring-valued sheaf underlying a commutative-ring-valued sheaf. -/
abbrev ringSheaf (A : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (CommRingSheaves.forgetRing (J := J)).obj A

/-- The internal ring obtained after forgetting multiplicative commutativity. -/
abbrev ringObject (A : Sheaf J CommRingCat.{w}) : InternalRing.RingObjects J :=
  InternalRing.toInternalObj (ringSheaf A)

/-- Sectionwise multiplicative commutativity makes the associated internal ring commutative. -/
theorem isCommMonObj (A : Sheaf J CommRingCat.{w}) :
    @IsCommMonObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.RingObjects.carrier J (ringObject A))
      (InternalRing.RingObjects.ringObj J (ringObject A)).toMonObj := sorry

/-- The internal commutative-ring structure refining the ring-level conversion. -/
@[implicit_reducible]
noncomputable def commRingObj (A : Sheaf J CommRingCat.{w}) :
    @CommRingObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.RingObjects.carrier J (ringObject A)) :=
  @CommRingObj.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.RingObjects.carrier J (ringObject A))
    (InternalRing.RingObjects.ringObj J (ringObject A)) (isCommMonObj A)

end ToInternal

/-- Convert a commutative-ring-valued sheaf to an internal commutative-ring object. -/
noncomputable def toInternalObj (A : Sheaf J CommRingCat.{w}) : CommRingObjects J :=
  @CommRingObjCat.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.RingObjects.carrier J (ToInternal.ringObject A))
    (ToInternal.commRingObj A)

/-- Convert a morphism of commutative-ring-valued sheaves to an internal commutative-ring
morphism. -/
noncomputable def toInternalMap {A B : Sheaf J CommRingCat.{w}} (f : A ⟶ B) :
    CommRingObjects.Hom J (toInternalObj A) (toInternalObj B) :=
  (CommRingObjects.fullyFaithfulForgetRing J).preimage
    (InternalRing.toInternalMap ((CommRingSheaves.forgetRing (J := J)).map f))

/-- Conversion to internal commutative rings preserves identity morphisms. -/
theorem toInternalMap_id (A : Sheaf J CommRingCat.{w}) :
    toInternalMap (𝟙 A) = 𝟙 (toInternalObj A) := sorry

/-- Conversion to internal commutative rings preserves composition. -/
theorem toInternalMap_comp {A B D : Sheaf J CommRingCat.{w}}
    (f : A ⟶ B) (g : B ⟶ D) :
    toInternalMap (f ≫ g) = CommRingObjects.comp J (toInternalMap f) (toInternalMap g) := sorry

/-- The functor from commutative-ring-valued sheaves to internal commutative rings. -/
@[stacks 0FRE "commutative-ring-valued sheaves as internal commutative rings"]
noncomputable def toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J where
  obj := toInternalObj
  map := toInternalMap
  map_id := toInternalMap_id
  map_comp := toInternalMap_comp

/-- Naturality of the ring-level comparison for conversion to internal commutative rings. -/
theorem toInternalForgetRing_naturality {A B : Sheaf J CommRingCat.{w}} (f : A ⟶ B) :
    (((toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (CommRingObjects.forgetRing J :
          CommRingObjects J ⥤ InternalRing.RingObjects J)).map f) ≫
        𝟙 ((CommRingObjects.forgetRing J).obj (toInternalObj B)) =
      𝟙 ((CommRingObjects.forgetRing J).obj (toInternalObj A)) ≫
        ((CommRingSheaves.forgetRing (J := J) ⋙
          (InternalRing.toInternal :
            Sheaf J RingCat.{w} ⥤ InternalRing.RingObjects J)).map f) := sorry

/-- Forgetting commutativity after `toInternal` recovers the ring-level conversion. -/
noncomputable def toInternalForgetRingIso :
    (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (CommRingObjects.forgetRing J :
          CommRingObjects J ⥤ InternalRing.RingObjects J) ≅
      CommRingSheaves.forgetRing (J := J) ⋙
        (InternalRing.toInternal :
          Sheaf J RingCat.{w} ⥤ InternalRing.RingObjects J) :=
  NatIso.ofComponents
    (fun A ↦ Iso.refl ((CommRingObjects.forgetRing J).obj (toInternalObj A)))
    (fun f ↦ toInternalForgetRing_naturality f)

/-- Naturality of the carrier comparison for conversion to internal commutative rings. -/
theorem toInternalForget_naturality [J.HasSheafCompose (forget CommRingCat.{w})]
    {A B : Sheaf J CommRingCat.{w}} (f : A ⟶ B) :
    ((toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (CommRingObjects.forget J : CommRingObjects J ⥤ Sheaf J (Type w))).map f ≫
        (InternalRing.toInternalForgetIso.app (ToInternal.ringSheaf B)).hom =
      (InternalRing.toInternalForgetIso.app (ToInternal.ringSheaf A)).hom ≫
        (sheafCompose J (forget CommRingCat.{w})).map f := sorry

/-- Forgetting the internal commutative ring produced by `toInternal` recovers the ordinary
underlying type-valued sheaf. -/
noncomputable def toInternalForgetIso [J.HasSheafCompose (forget CommRingCat.{w})] :
    (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (CommRingObjects.forget J : CommRingObjects J ⥤ Sheaf J (Type w)) ≅
      sheafCompose J (forget CommRingCat.{w}) :=
  NatIso.ofComponents
    (fun A ↦ InternalRing.toInternalForgetIso.app (ToInternal.ringSheaf A))
    (fun f ↦ toInternalForget_naturality f)

end ToInternal

namespace FromInternal

variable (R : CommRingObjects J) (U : Cᵒᵖ)

/-- The internal ring obtained by forgetting multiplicative commutativity. -/
abbrev ringObject (R : CommRingObjects J) : InternalRing.RingObjects J :=
  (CommRingObjects.forgetRing J).obj R

/-- The underlying type-valued sheaf of an internal commutative ring. -/
abbrev sheaf (R : CommRingObjects J) : Sheaf J (Type w) :=
  InternalRing.FromInternal.sheaf (ringObject R)

/-- Multiplication on reconstructed sections is commutative. -/
theorem mulComm (a b : (sheaf R).obj.obj U) :
    InternalRing.FromInternal.mul (ringObject R) U a b =
      InternalRing.FromInternal.mul (ringObject R) U b a := sorry

/-- The explicit commutative-ring structure reconstructed on a section type. -/
@[implicit_reducible]
noncomputable def commRing : CommRing ((sheaf R).obj.obj U) where
  __ := InternalRing.FromInternal.ring (ringObject R) U
  mul_comm := mulComm R U

/-- The bundled commutative ring of sections reconstructed from an internal commutative ring. -/
noncomputable def obj : CommRingCat.{w} :=
  @CommRingCat.of ((sheaf R).obj.obj U) (commRing R U)

variable {U V : Cᵒᵖ}

/-- The morphism of commutative section rings induced by a restriction map. -/
noncomputable def map (f : U ⟶ V) : obj R U ⟶ obj R V :=
  @CommRingCat.ofHom ((sheaf R).obj.obj U) ((sheaf R).obj.obj V)
    (commRing R U) (commRing R V) (InternalRing.FromInternal.mapRingHom (ringObject R) f)

/-- Reconstructed restriction maps preserve identities. -/
theorem mapId (U : Cᵒᵖ) : map R (𝟙 U) = 𝟙 (obj R U) := sorry

/-- Reconstructed restriction maps preserve composition. -/
theorem mapComp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    map R (f ≫ g) = map R f ≫ map R g := sorry

/-- The commutative-ring-valued presheaf reconstructed from an internal commutative ring. -/
noncomputable def presheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj := obj R
  map := map R
  map_id := mapId R
  map_comp := mapComp R

/-- The reconstructed commutative-ring-valued presheaf satisfies the sheaf condition. -/
theorem isSheaf : Presheaf.IsSheaf J (presheaf R) := sorry

end FromInternal

/-- Reconstruct a commutative-ring-valued sheaf from an internal commutative ring. -/
noncomputable def fromInternalObj (R : CommRingObjects J) : Sheaf J CommRingCat.{w} :=
  ⟨FromInternal.presheaf R, FromInternal.isSheaf R⟩

namespace FromInternal

variable {R S : CommRingObjects J} (f : CommRingObjects.Hom J R S)

/-- The underlying morphism of internal rings. -/
abbrev ringHom : InternalRing.RingObjects.Hom J (ringObject R) (ringObject S) :=
  (CommRingObjects.forgetRing J).map f

/-- The component on sections of the reconstructed morphism of commutative-ring-valued
presheaves. -/
noncomputable def homApp (U : Cᵒᵖ) : obj R U ⟶ obj S U :=
  @CommRingCat.ofHom ((sheaf R).obj.obj U) ((sheaf S).obj.obj U)
    (commRing R U) (commRing S U) (InternalRing.FromInternal.homRingHom (ringHom f) U)

/-- The reconstructed components of an internal commutative-ring morphism are natural. -/
theorem homNaturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    map R g ≫ homApp f V = homApp f U ≫ map S g := sorry

/-- The morphism of commutative-ring-valued presheaves reconstructed from an internal
commutative-ring morphism. -/
noncomputable def presheafMap : presheaf R ⟶ presheaf S where
  app := homApp f
  naturality := fun {_ _} g ↦ homNaturality f g

end FromInternal

/-- Reconstruct a morphism of commutative-ring-valued sheaves from an internal
commutative-ring morphism. -/
noncomputable def fromInternalMap {R S : CommRingObjects J} (f : CommRingObjects.Hom J R S) :
    fromInternalObj R ⟶ fromInternalObj S :=
  ObjectProperty.homMk (FromInternal.presheafMap f)

/-- Reconstruction from internal commutative rings preserves identity morphisms. -/
theorem fromInternalMap_id (R : CommRingObjects J) :
    fromInternalMap (𝟙 R) = 𝟙 (fromInternalObj R) := sorry

/-- Reconstruction from internal commutative rings preserves composition. -/
theorem fromInternalMap_comp {R S T : CommRingObjects J}
    (f : CommRingObjects.Hom J R S) (g : CommRingObjects.Hom J S T) :
    fromInternalMap (CommRingObjects.comp J f g) = fromInternalMap f ≫ fromInternalMap g := sorry

/-- The functor reconstructing commutative-ring-valued sheaves from internal commutative rings. -/
@[stacks 0FRE "reconstructing commutative-ring-valued sheaves"]
noncomputable def fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w} where
  obj := fromInternalObj
  map := fromInternalMap
  map_id := fromInternalMap_id
  map_comp := fromInternalMap_comp

section ForgetComparisons

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Forgetting commutativity after reconstruction recovers ring-valued reconstruction. -/
noncomputable def fromInternalForgetRingIso :
    (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
        CommRingSheaves.forgetRing (J := J) ≅
      (CommRingObjects.forgetRing J :
          CommRingObjects J ⥤ InternalRing.RingObjects J) ⋙
        (InternalRing.fromInternal :
          InternalRing.RingObjects J ⥤ Sheaf J RingCat.{w}) :=
  Iso.refl _

variable [J.HasSheafCompose (forget RingCat.{w})]
variable [J.HasSheafCompose (forget CommRingCat.{w})]

/-- Naturality of the carrier comparison for reconstruction from internal commutative rings. -/
theorem fromInternalForget_naturality {R S : CommRingObjects J}
    (f : CommRingObjects.Hom J R S) :
    ((fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
        sheafCompose J (forget CommRingCat.{w})).map f ≫
        (InternalRing.fromInternalForgetIso.app (FromInternal.ringObject S)).hom =
      (InternalRing.fromInternalForgetIso.app (FromInternal.ringObject R)).hom ≫
        (CommRingObjects.forget J).map f := sorry

/-- Forgetting reconstructed commutative-ring-valued sheaves recovers the underlying
type-valued sheaf. -/
noncomputable def fromInternalForgetIso :
    (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
        sheafCompose J (forget CommRingCat.{w}) ≅
      (CommRingObjects.forget J : CommRingObjects J ⥤ Sheaf J (Type w)) :=
  NatIso.ofComponents
    (fun R ↦ InternalRing.fromInternalForgetIso.app (FromInternal.ringObject R))
    (fun f ↦ fromInternalForget_naturality f)

end ForgetComparisons

section Comparison

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget RingCat.{w})]

namespace Comparison

/-- The internal commutative-ring comparison obtained by lifting the ring-level reconstruction
comparison through the canonical fully faithful forgetful functor. -/
noncomputable def fromToAppIso (R : CommRingObjects J) :
    ((fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
      (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J)).obj R ≅ R :=
  (CommRingObjects.fullyFaithfulForgetRing J).preimageIso
      ((InternalRing.fromToIso :
        (InternalRing.fromInternal :
            InternalRing.RingObjects J ⥤ Sheaf J RingCat.{w}) ⋙
          (InternalRing.toInternal :
            Sheaf J RingCat.{w} ⥤ InternalRing.RingObjects J) ≅
          𝟭 (InternalRing.RingObjects J)).app (FromInternal.ringObject R))

/-- The internal commutative-ring reconstruction comparison is natural. -/
theorem fromToNaturality {R S : CommRingObjects J} (f : CommRingObjects.Hom J R S) :
    ((fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
        (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J)).map f ≫
      (fromToAppIso S).hom =
      (fromToAppIso R).hom ≫ (𝟭 (CommRingObjects J)).map f := sorry

/-- The commutative-ring-valued-sheaf comparison obtained by lifting the ring-level reconstruction
comparison through the canonical fully faithful sheaf forgetful functor. -/
noncomputable def toFromAppIso (A : Sheaf J CommRingCat.{w}) :
    ((toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
      (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w})).obj A ≅ A :=
  (CommRingSheaves.fullyFaithfulForgetRing (J := J)).preimageIso
    ((InternalRing.toFromIso :
      (InternalRing.toInternal :
          Sheaf J RingCat.{w} ⥤ InternalRing.RingObjects J) ⋙
        (InternalRing.fromInternal :
          InternalRing.RingObjects J ⥤ Sheaf J RingCat.{w}) ≅
        𝟭 (Sheaf J RingCat.{w})).app (ToInternal.ringSheaf A))

/-- The commutative-ring-valued-sheaf reconstruction comparison is natural. -/
theorem toFromNaturality {A B : Sheaf J CommRingCat.{w}} (f : A ⟶ B) :
    ((toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w})).map f ≫
      (toFromAppIso B).hom =
      (toFromAppIso A).hom ≫ (𝟭 (Sheaf J CommRingCat.{w})).map f := sorry

end Comparison

/-- Reconstructing a commutative-ring-valued sheaf and converting it back recovers the internal
commutative ring. -/
noncomputable def fromToIso :
    (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ⋙
        (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ≅
      𝟭 (CommRingObjects J) :=
  NatIso.ofComponents Comparison.fromToAppIso Comparison.fromToNaturality

/-- Converting a commutative-ring-valued sheaf to an internal commutative ring and reconstructing
it recovers the sheaf. -/
noncomputable def toFromIso :
    (toInternal : Sheaf J CommRingCat.{w} ⥤ CommRingObjects J) ⋙
        (fromInternal : CommRingObjects J ⥤ Sheaf J CommRingCat.{w}) ≅
      𝟭 (Sheaf J CommRingCat.{w}) :=
  NatIso.ofComponents Comparison.toFromAppIso Comparison.toFromNaturality

/-- The two reconstruction comparisons satisfy the triangle identity on internal commutative
rings. -/
theorem equivalence_triangle (A : Sheaf J CommRingCat.{w}) :
    toInternal.map (toFromIso.inv.app A) ≫ fromToIso.hom.app (toInternal.obj A) =
      𝟙 (toInternal.obj A) := sorry

/-- Commutative-ring-valued sheaves are equivalent to internal commutative-ring objects in
type-valued sheaves. -/
@[stacks 0FRE "commutative-ring-valued sheaves and internal commutative rings"]
noncomputable def equivalence : Sheaf J CommRingCat.{w} ≌ CommRingObjects J where
  functor := toInternal
  inverse := fromInternal
  unitIso := toFromIso.symm
  counitIso := fromToIso
  functor_unitIso_comp := equivalence_triangle

end Comparison

/- Every non-Prop field below is built explicitly from the ring-level equivalence or from the two
canonical fully faithful forgetful functors.  Any reported `sorryAx` is confined to multiplicative
commutativity, functoriality, naturality, sheaf conditions, and equivalence coherence. -/

end CategoryTheory.Sheaf.InternalCommRing
