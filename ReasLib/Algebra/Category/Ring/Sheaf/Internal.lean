/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Internal
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Ring-valued sheaves as internal ring objects

A sheaf of rings has an underlying type-valued sheaf whose ring operations are morphisms of
sheaves.  This module constructs the two conversions explicitly, reconstructing a ring-valued
sheaf from an internal ring by evaluating its operations sectionwise.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.AddMonObj CategoryTheory.MonObj

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.InternalRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The canonical braiding determined by the chosen finite products of type-valued sheaves. -/
noncomputable instance (priority := high) sheafBraidedCategory
    (J : GrothendieckTopology C) :
    BraidedCategory (Sheaf J (Type w)) :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Internal ring objects in the type-valued sheaf category, with the canonical cartesian
braiding fixed explicitly. -/
abbrev RingObjects (J : GrothendieckTopology C) :=
  @RingObjCat (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)

namespace RingObjects

/-- The underlying type-valued sheaf of an internal ring, with the fixed braiding supplied
explicitly. -/
abbrev carrier (J : GrothendieckTopology C) (R : RingObjects J) : Sheaf J (Type w) :=
  @RingObjCat.X (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) R

/-- The internal ring structure carried by an object of `RingObjects J`, with no ambient
braiding instance required at the call site. -/
abbrev ringObj (J : GrothendieckTopology C) (R : RingObjects J) :
    @RingObj (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) (carrier J R) :=
  @RingObjCat.ringObj (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) R

/-- Morphisms between internal rings in type-valued sheaves, with the canonical braiding fixed. -/
abbrev Hom (J : GrothendieckTopology C) (R S : RingObjects J) :=
  @RingObjCat.Hom (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) R S

/-- The underlying morphism of type-valued sheaves of a morphism in `RingObjects J`. -/
abbrev hom (J : GrothendieckTopology C) {R S : RingObjects J} (f : Hom J R S) :
    carrier J R ⟶ carrier J S :=
  @RingObjCat.Hom.hom (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) R S f

/-- The category structure on internal rings in type-valued sheaves, using the fixed
cartesian braiding. -/
noncomputable instance (priority := high) category (J : GrothendieckTopology C) :
    Category (RingObjects J) :=
  @RingObjCat.instCategory (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)

/-- Forget an internal ring in type-valued sheaves to its underlying sheaf. -/
def forget (J : GrothendieckTopology C) : RingObjects J ⥤ Sheaf J (Type w) where
  obj := carrier J
  map := hom J

/-- Composition of morphisms between internal rings in type-valued sheaves. -/
def comp (J : GrothendieckTopology C) {R S T : RingObjects J}
    (f : Hom J R S) (g : Hom J S T) : Hom J R T :=
  @CategoryStruct.comp (RingObjects J)
    (@Category.toCategoryStruct (RingObjects J) (category J)) R S T f g

end RingObjects

section ToInternal

variable [J.HasSheafCompose (forget RingCat.{w})]

/-- The type-valued sheaf underlying a ring-valued sheaf. -/
abbrev underlying (R : Sheaf J RingCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget RingCat.{w})).obj R

/-- The zero section at one object of the site. -/
def zeroApp (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.obj U ⟶
      (underlying R).obj.obj U :=
  ↾fun _ ↦ (0 : R.obj.obj U)

/-- Naturality of the zero sections of a ring-valued sheaf. -/
theorem zeroApp_naturality (R : Sheaf J RingCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.map f ≫ zeroApp R V =
      zeroApp R U ≫ (underlying R).obj.map f := by
  ext x
  change (0 : R.obj.obj V) = (R.obj.map f).hom 0
  exact (map_zero (R.obj.map f).hom).symm

/-- The zero operation of the internal ring underlying a ring-valued sheaf. -/
def zero (R : Sheaf J RingCat.{w}) :
    𝟙_ (Sheaf J (Type w)) ⟶ underlying R :=
  ObjectProperty.homMk
    { app := zeroApp R
      naturality := fun {_ _} f ↦ zeroApp_naturality (C := C) (J := J) R f }

/-- The unit section at one object of the site. -/
def oneApp (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.obj U ⟶
      (underlying R).obj.obj U :=
  ↾fun _ ↦ (1 : R.obj.obj U)

/-- Naturality of the unit sections of a ring-valued sheaf. -/
theorem oneApp_naturality (R : Sheaf J RingCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.map f ≫ oneApp R V =
      oneApp R U ≫ (underlying R).obj.map f := by
  ext x
  change (1 : R.obj.obj V) = (R.obj.map f).hom 1
  exact (map_one (R.obj.map f).hom).symm

/-- The multiplicative unit of the internal ring underlying a ring-valued sheaf. -/
def one (R : Sheaf J RingCat.{w}) : 𝟙_ (Sheaf J (Type w)) ⟶ underlying R :=
  ObjectProperty.homMk
    { app := oneApp R
      naturality := fun {_ _} f ↦ oneApp_naturality (C := C) (J := J) R f }

/-- Addition on the ring of sections over one site object. -/
def sectionAdd (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    R.obj.obj U → R.obj.obj U → R.obj.obj U :=
  fun x y ↦ x + y

/-- Sectionwise addition at one object of the site. -/
def addApp (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    ((underlying R) ⊗ (underlying R)).obj.obj U ⟶ (underlying R).obj.obj U :=
  ↾fun x ↦ sectionAdd R U x.1 x.2

/-- Naturality of sectionwise addition. -/
theorem addApp_naturality (R : Sheaf J RingCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((underlying R) ⊗ (underlying R)).obj.map f ≫ addApp R V =
      addApp R U ≫ (underlying R).obj.map f := by
  ext x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change (R.obj.map f).hom x.1 + (R.obj.map f).hom x.2 = (R.obj.map f).hom (x.1 + x.2)
  exact (map_add (R.obj.map f).hom x.1 x.2).symm

/-- The addition of the internal ring underlying a ring-valued sheaf. -/
def add (R : Sheaf J RingCat.{w}) : underlying R ⊗ underlying R ⟶ underlying R :=
  ObjectProperty.homMk
    { app := addApp R
      naturality := fun {_ _} f ↦ addApp_naturality (C := C) (J := J) R f }

/-- Multiplication on the ring of sections over one site object. -/
def sectionMul (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    R.obj.obj U → R.obj.obj U → R.obj.obj U :=
  fun x y ↦ x * y

/-- Sectionwise multiplication at one object of the site. -/
def mulApp (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    ((underlying R) ⊗ (underlying R)).obj.obj U ⟶ (underlying R).obj.obj U :=
  ↾fun x ↦ sectionMul R U x.1 x.2

/-- Naturality of sectionwise multiplication. -/
theorem mulApp_naturality (R : Sheaf J RingCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((underlying R) ⊗ (underlying R)).obj.map f ≫ mulApp R V =
      mulApp R U ≫ (underlying R).obj.map f := by
  ext x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change (R.obj.map f).hom x.1 * (R.obj.map f).hom x.2 = (R.obj.map f).hom (x.1 * x.2)
  exact (map_mul (R.obj.map f).hom x.1 x.2).symm

/-- The multiplication of the internal ring underlying a ring-valued sheaf. -/
def mul (R : Sheaf J RingCat.{w}) : underlying R ⊗ underlying R ⟶ underlying R :=
  ObjectProperty.homMk
    { app := mulApp R
      naturality := fun {_ _} f ↦ mulApp_naturality (C := C) (J := J) R f }

/-- Negation on the ring of sections over one site object. -/
def sectionNeg (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    R.obj.obj U → R.obj.obj U :=
  fun x ↦ -x

/-- Sectionwise negation at one object of the site. -/
def negApp (R : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    (underlying R).obj.obj U ⟶ (underlying R).obj.obj U :=
  ↾fun x ↦ sectionNeg R U x

/-- Naturality of sectionwise negation. -/
theorem negApp_naturality (R : Sheaf J RingCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (underlying R).obj.map f ≫ negApp R V =
      negApp R U ≫ (underlying R).obj.map f := by
  ext x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change -(R.obj.map f).hom x = (R.obj.map f).hom (-x)
  exact (map_neg (R.obj.map f).hom x).symm

/-- The negation of the internal ring underlying a ring-valued sheaf. -/
def neg (R : Sheaf J RingCat.{w}) : underlying R ⟶ underlying R :=
  ObjectProperty.homMk
    { app := negApp R
      naturality := fun {_ _} f ↦ negApp_naturality (C := C) (J := J) R f }

/-- Sectionwise zero is a left identity for sectionwise addition. -/
theorem zero_add (R : Sheaf J RingCat.{w}) :
    zero R ▷ underlying R ≫ add R = (λ_ (underlying R)).hom := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change 0 + x.2 = x.2
  exact _root_.zero_add x.2

/-- Sectionwise zero is a right identity for sectionwise addition. -/
theorem add_zero (R : Sheaf J RingCat.{w}) :
    underlying R ◁ zero R ≫ add R = (ρ_ (underlying R)).hom := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change x.1 + 0 = x.1
  exact _root_.add_zero x.1

/-- Sectionwise addition is associative. -/
theorem add_assoc (R : Sheaf J RingCat.{w}) :
    (add R ▷ underlying R) ≫ add R =
      (α_ (underlying R) (underlying R) (underlying R)).hom ≫
        (underlying R ◁ add R) ≫ add R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change (x.1.1 + x.1.2) + x.2 = x.1.1 + (x.1.2 + x.2)
  exact _root_.add_assoc x.1.1 x.1.2 x.2

/-- The additive-monoid structure on the underlying sheaf of a ring-valued sheaf. -/
@[implicit_reducible]
def addMonObj (R : Sheaf J RingCat.{w}) : AddMonObj (underlying R) where
  zero := zero R
  add := add R
  zero_add := zero_add R
  add_zero := add_zero R
  add_assoc := add_assoc R

/-- Sectionwise negation is a left additive inverse. -/
theorem neg_add (R : Sheaf J RingCat.{w}) :
    lift (neg R) (𝟙 (underlying R)) ≫ add R =
      toUnit (underlying R) ≫ zero R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change -x + x = (0 : R.obj.obj U)
  exact neg_add_cancel x

/-- Sectionwise negation is a right additive inverse. -/
theorem add_neg (R : Sheaf J RingCat.{w}) :
    lift (𝟙 (underlying R)) (neg R) ≫ add R =
      toUnit (underlying R) ≫ zero R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change x + -x = (0 : R.obj.obj U)
  exact add_neg_cancel x

/-- The additive-group structure on the underlying sheaf of a ring-valued sheaf. -/
@[implicit_reducible]
def addGrpObj (R : Sheaf J RingCat.{w}) : AddGrpObj (underlying R) where
  toAddMonObj := addMonObj R
  neg := neg R
  left_neg := neg_add R
  right_neg := add_neg R

/-- Sectionwise addition is commutative. -/
theorem add_comm (R : Sheaf J RingCat.{w}) :
    (β_ (underlying R) (underlying R)).hom ≫ add R = add R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change x.2 + x.1 = (x.1 + x.2 : R.obj.obj U)
  exact _root_.add_comm x.2 x.1

/-- The commutativity witness for the additive structure of a ring-valued sheaf. -/
theorem isCommAddMonObj (R : Sheaf J RingCat.{w}) :
    @IsCommAddMonObj (Sheaf J (Type w)) _ _ _ (underlying R) (addMonObj R) := by
  letI := addMonObj R
  exact ⟨add_comm R⟩

/-- The unit section is a left identity for sectionwise multiplication. -/
theorem one_mul (R : Sheaf J RingCat.{w}) :
    one R ▷ underlying R ≫ mul R = (λ_ (underlying R)).hom := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change 1 * x.2 = x.2
  exact _root_.one_mul x.2

/-- The unit section is a right identity for sectionwise multiplication. -/
theorem mul_one (R : Sheaf J RingCat.{w}) :
    underlying R ◁ one R ≫ mul R = (ρ_ (underlying R)).hom := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change x.1 * 1 = x.1
  exact _root_.mul_one x.1

/-- Sectionwise multiplication is associative. -/
theorem mul_assoc (R : Sheaf J RingCat.{w}) :
    (mul R ▷ underlying R) ≫ mul R =
      (α_ (underlying R) (underlying R) (underlying R)).hom ≫
        (underlying R ◁ mul R) ≫ mul R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change (x.1.1 * x.1.2) * x.2 = x.1.1 * (x.1.2 * x.2)
  exact _root_.mul_assoc x.1.1 x.1.2 x.2

/-- The multiplicative-monoid structure on the underlying sheaf of a ring-valued sheaf. -/
@[implicit_reducible]
def monObj (R : Sheaf J RingCat.{w}) : MonObj (underlying R) where
  one := one R
  mul := mul R
  one_mul := one_mul R
  mul_one := mul_one R
  mul_assoc := mul_assoc R

/-- Sectionwise multiplication distributes over addition on the left. -/
theorem mul_add (R : Sheaf J RingCat.{w}) :
    underlying R ◁ add R ≫ mul R =
      lift ((underlying R ◁ fst _ _) ≫ mul R)
          ((underlying R ◁ snd _ _) ≫ mul R) ≫ add R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change x.1 * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
  exact _root_.mul_add x.1 x.2.1 x.2.2

/-- Sectionwise multiplication distributes over addition on the right. -/
theorem add_mul (R : Sheaf J RingCat.{w}) :
    add R ▷ underlying R ≫ mul R =
      lift (fst _ _ ▷ underlying R ≫ mul R)
          (snd _ _ ▷ underlying R ≫ mul R) ≫ add R := by
  ext U x
  letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
  change (x.1.1 + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
  exact _root_.add_mul x.1.1 x.1.2 x.2

/-- The internal ring carried by the type-valued sheaf underlying a ring-valued sheaf. -/
@[implicit_reducible]
def ringObj (R : Sheaf J RingCat.{w}) :
    @RingObj (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) (underlying R) :=
  @RingObj.mk (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) (underlying R)
    (addGrpObj R) (isCommAddMonObj R) (monObj R) (mul_add R) (add_mul R)

/-- A morphism of ring-valued sheaves is a morphism of their internal rings after forgetting
coefficients. -/
theorem toInternal_isRingHom {R S : Sheaf J RingCat.{w}} (f : R ⟶ S) :
    @IsRingHom (Sheaf J (Type w)) _ _ (underlying R) (underlying S)
      (addMonObj R) (addMonObj S) (monObj R) (monObj S)
      ((sheafCompose J (forget RingCat.{w})).map f) := by
  refine @IsRingHom.mk (Sheaf J (Type w)) _ _ (underlying R) (underlying S)
    (addMonObj R) (addMonObj S) (monObj R) (monObj S) _
    (@IsAddMonHom.mk (Sheaf J (Type w)) _ _ (underlying R) (underlying S)
      (addMonObj R) (addMonObj S) _ ?_ ?_)
    (@IsMonHom.mk (Sheaf J (Type w)) _ _ (underlying R) (underlying S)
      (monObj R) (monObj S) _ ?_ ?_)
  · ext U x
    exact map_zero (f.hom.app U).hom
  · ext U x
    letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
    exact map_add (f.hom.app U).hom x.1 x.2
  · ext U x
    exact map_one (f.hom.app U).hom
  · ext U x
    letI : Ring ((underlying R).obj.obj U) := RingCat.ring (R.obj.obj U)
    exact map_mul (f.hom.app U).hom x.1 x.2

/-- Forget a ring-valued sheaf to its canonically associated internal ring object. -/
def toInternalObj (R : Sheaf J RingCat.{w}) : RingObjects J :=
  @RingObjCat.mk (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)
    (underlying R) (ringObj R)

/-- The internal-ring morphism induced by a morphism of ring-valued sheaves. -/
def toInternalMap {R S : Sheaf J RingCat.{w}} (f : R ⟶ S) :
    RingObjects.Hom J (toInternalObj R) (toInternalObj S) :=
  @RingObjCat.Hom.mk (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)
    (toInternalObj R) (toInternalObj S)
    ((sheafCompose J (forget RingCat.{w})).map f) (toInternal_isRingHom f)

/-- The internal-ring conversion preserves identity morphisms. -/
theorem toInternalMap_id (R : Sheaf J RingCat.{w}) :
    toInternalMap (𝟙 R) = 𝟙 (toInternalObj R) := by
  apply RingObjCat.Hom.ext
  exact (sheafCompose J (forget RingCat.{w})).map_id R

/-- The internal-ring conversion preserves composition. -/
theorem toInternalMap_comp {R S T : Sheaf J RingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ T) :
    toInternalMap (f ≫ g) =
      RingObjects.comp J (toInternalMap f) (toInternalMap g) := by
  apply RingObjCat.Hom.ext
  exact (sheafCompose J (forget RingCat.{w})).map_comp f g

/-- The functor from ring-valued sheaves to internal ring objects in type-valued sheaves. -/
def toInternal : Sheaf J RingCat.{w} ⥤ RingObjects J where
  obj := toInternalObj
  map := toInternalMap
  map_id := toInternalMap_id
  map_comp := toInternalMap_comp

/-- Forgetting the internal ring produced by `toInternal` is definitionally the usual
coefficient-forgetful functor on sheaves. -/
def toInternalForgetIso :
    toInternal ⋙
        (RingObjects.forget J : RingObjects J ⥤ Sheaf J (Type w)) ≅
      sheafCompose J (forget RingCat.{w}) :=
  Iso.refl _

end ToInternal

namespace FromInternal

variable (R : RingObjects J) (U : Cᵒᵖ)

/-- The underlying sheaf of an internal ring, accessed without synthesizing a braiding. -/
abbrev sheaf (R : RingObjects J) : Sheaf J (Type w) := RingObjects.carrier J R

/-- The ring structure of an internal ring sheaf, accessed with its fixed braiding. -/
abbrev data (R : RingObjects J) :
    @RingObj (Sheaf J (Type w)) _ _ (sheafBraidedCategory J) (sheaf R) :=
  RingObjects.ringObj J R

/-- The zero element on a section type of an internal ring sheaf. -/
def zero : (sheaf R).obj.obj U :=
  (data R).toAddGrpObj.toAddMonObj.zero.hom.app U PUnit.unit

/-- The multiplicative unit on a section type of an internal ring sheaf. -/
def one : (sheaf R).obj.obj U :=
  (data R).toMonObj.one.hom.app U PUnit.unit

/-- Addition on a section type of an internal ring sheaf. -/
def add (x y : (sheaf R).obj.obj U) : (sheaf R).obj.obj U :=
  (data R).toAddGrpObj.toAddMonObj.add.hom.app U (x, y)

/-- Multiplication on a section type of an internal ring sheaf. -/
def mul (x y : (sheaf R).obj.obj U) : (sheaf R).obj.obj U :=
  (data R).toMonObj.mul.hom.app U (x, y)

/-- Negation on a section type of an internal ring sheaf. -/
def neg (x : (sheaf R).obj.obj U) : (sheaf R).obj.obj U :=
  (data R).toAddGrpObj.neg.hom.app U x

/-- The explicit addition operation used to reconstruct a section ring. -/
@[implicit_reducible]
def addData : Add ((sheaf R).obj.obj U) := ⟨add R U⟩

/-- The explicit multiplication operation used to reconstruct a section ring. -/
@[implicit_reducible]
def mulData : Mul ((sheaf R).obj.obj U) := ⟨mul R U⟩

/-- The explicit negation operation used to reconstruct a section ring. -/
@[implicit_reducible]
def negData : Neg ((sheaf R).obj.obj U) := ⟨neg R U⟩

/-- The explicit zero used to reconstruct a section ring. -/
@[implicit_reducible]
def zeroData : Zero ((sheaf R).obj.obj U) := ⟨zero R U⟩

/-- The explicit multiplicative unit used to reconstruct a section ring. -/
@[implicit_reducible]
def oneData : One ((sheaf R).obj.obj U) := ⟨one R U⟩

/-- Sectionwise addition reconstructed from an internal ring is associative. -/
theorem addAssoc (a b c : (sheaf R).obj.obj U) :
    add R U (add R U a b) c = add R U a (add R U b c) := by
  exact congrArg (fun f ↦ f.hom.app U ((a, b), c))
    ((data R).toAddGrpObj.toAddMonObj.add_assoc)

/-- Sectionwise zero reconstructed from an internal ring is a left additive identity. -/
theorem zeroAdd (a : (sheaf R).obj.obj U) : add R U (zero R U) a = a := by
  exact congrArg (fun f ↦ f.hom.app U (PUnit.unit, a))
    ((data R).toAddGrpObj.toAddMonObj.zero_add)

/-- Sectionwise negation reconstructed from an internal ring is a left additive inverse. -/
theorem negAddCancel (a : (sheaf R).obj.obj U) :
    add R U (neg R U a) a = zero R U := by
  exact congrArg (fun f ↦ f.hom.app U a) ((data R).toAddGrpObj.left_neg)

/-- Sectionwise multiplication reconstructed from an internal ring is associative. -/
theorem mulAssoc (a b c : (sheaf R).obj.obj U) :
    mul R U (mul R U a b) c = mul R U a (mul R U b c) := by
  exact congrArg (fun f ↦ f.hom.app U ((a, b), c)) ((data R).toMonObj.mul_assoc)

/-- Sectionwise one reconstructed from an internal ring is a left multiplicative identity. -/
theorem oneMul (a : (sheaf R).obj.obj U) : mul R U (one R U) a = a := by
  exact congrArg (fun f ↦ f.hom.app U (PUnit.unit, a)) ((data R).toMonObj.one_mul)

/-- Sectionwise one reconstructed from an internal ring is a right multiplicative identity. -/
theorem mulOne (a : (sheaf R).obj.obj U) : mul R U a (one R U) = a := by
  exact congrArg (fun f ↦ f.hom.app U (a, PUnit.unit)) ((data R).toMonObj.mul_one)

/-- Sectionwise multiplication reconstructed from an internal ring distributes on the left. -/
theorem mulAdd (a b c : (sheaf R).obj.obj U) :
    mul R U a (add R U b c) = add R U (mul R U a b) (mul R U a c) := by
  exact congrArg (fun f ↦ f.hom.app U (a, (b, c))) ((data R).mul_add)

/-- Sectionwise multiplication reconstructed from an internal ring distributes on the right. -/
theorem addMul (a b c : (sheaf R).obj.obj U) :
    mul R U (add R U a b) c = add R U (mul R U a c) (mul R U b c) := by
  exact congrArg (fun f ↦ f.hom.app U ((a, b), c)) ((data R).add_mul)

/-- The ring of sections reconstructed explicitly from an internal ring sheaf. -/
@[implicit_reducible]
noncomputable def ring : Ring ((sheaf R).obj.obj U) :=
  @Ring.ofMinimalAxioms ((sheaf R).obj.obj U) (addData R U) (mulData R U) (negData R U)
    (zeroData R U) (oneData R U) (addAssoc R U) (zeroAdd R U) (negAddCancel R U)
    (mulAssoc R U) (oneMul R U) (mulOne R U) (mulAdd R U) (addMul R U)

/-- The bundled ring of sections of an internal ring sheaf. -/
noncomputable def obj : RingCat.{w} :=
  @RingCat.of ((sheaf R).obj.obj U) (ring R U)

variable {U} {V : Cᵒᵖ}

/-- Restriction maps preserve the reconstructed zero section. -/
theorem mapZero (f : U ⟶ V) : (sheaf R).obj.map f (zero R U) = zero R V := by
  exact (congrArg (fun f ↦ f PUnit.unit)
    ((data R).toAddGrpObj.toAddMonObj.zero.hom.naturality f)).symm

/-- Restriction maps preserve the reconstructed multiplicative unit. -/
theorem mapOne (f : U ⟶ V) : (sheaf R).obj.map f (one R U) = one R V := by
  exact (congrArg (fun f ↦ f PUnit.unit)
    ((data R).toMonObj.one.hom.naturality f)).symm

/-- Restriction maps preserve reconstructed sectionwise addition. -/
theorem mapAdd (f : U ⟶ V) (x y : (sheaf R).obj.obj U) :
    (sheaf R).obj.map f (add R U x y) =
      add R V ((sheaf R).obj.map f x) ((sheaf R).obj.map f y) := by
  exact (congrArg (fun f ↦ f (x, y))
    ((data R).toAddGrpObj.toAddMonObj.add.hom.naturality f)).symm

/-- Restriction maps preserve reconstructed sectionwise multiplication. -/
theorem mapMul (f : U ⟶ V) (x y : (sheaf R).obj.obj U) :
    (sheaf R).obj.map f (mul R U x y) =
      mul R V ((sheaf R).obj.map f x) ((sheaf R).obj.map f y) := by
  exact (congrArg (fun f ↦ f (x, y)) ((data R).toMonObj.mul.hom.naturality f)).symm

/-- The ring homomorphism on sections induced by one restriction map. -/
noncomputable def mapRingHom (f : U ⟶ V) : obj R U →+* obj R V where
  toFun := (sheaf R).obj.map f
  map_one' := mapOne R f
  map_mul' := mapMul R f
  map_zero' := mapZero R f
  map_add' := mapAdd R f

/-- The morphism of bundled section rings induced by one restriction map. -/
noncomputable def map (f : U ⟶ V) : obj R U ⟶ obj R V :=
  @RingCat.ofHom ((sheaf R).obj.obj U) ((sheaf R).obj.obj V)
    (ring R U) (ring R V) (mapRingHom R f)

/-- Reconstructed restriction maps preserve identities. -/
theorem mapId (U : Cᵒᵖ) : map R (𝟙 U) = 𝟙 (obj R U) := by
  ext x
  exact congrArg (fun f ↦ f x) ((sheaf R).obj.map_id U)

/-- Reconstructed restriction maps preserve composition. -/
theorem mapComp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    map R (f ≫ g) = map R f ≫ map R g := by
  ext x
  exact congrArg (fun h ↦ h x) ((sheaf R).obj.map_comp f g)

/-- The ring-valued presheaf reconstructed from an internal ring sheaf. -/
noncomputable def presheaf : Cᵒᵖ ⥤ RingCat.{w} where
  obj := obj R
  map := map R
  map_id := mapId R
  map_comp := mapComp R

/-- The reconstructed ring-valued presheaf satisfies the sheaf condition. -/
theorem isSheaf : Presheaf.IsSheaf J (presheaf R) := by
  -- Glue each element of the test ring in the underlying sheaf, then use separatedness.
  intro E X T hT x hx
  have h := ((isSheaf_iff_isSheaf_of_type J (sheaf R).obj).mp (sheaf R).property) T hT
  let y (e : E) : Presieve.FamilyOfElements (sheaf R).obj T.arrows :=
    fun _ f hf ↦ (x f hf).hom e
  have hy (e : E) : (y e).Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    exact congrArg (fun g : E ⟶ obj R (.op Z) ↦ g.hom e) (hx g₁ g₂ hf₁ hf₂ heq)
  let a (e : E) : (sheaf R).obj.obj (.op X) := h.amalgamate (y e) (hy e)
  have ha (e : E) : (y e).IsAmalgamation (a e) := h.isAmalgamation (hy e)
  let g : E →+* obj R (.op X) :=
    { toFun := a
      map_one' := by
        apply h.isSeparatedFor.ext
        intro Y f hf
        change (sheaf R).obj.map f.op (a 1) = (sheaf R).obj.map f.op (one R (.op X))
        rw [ha 1 f hf, mapOne]
        exact (x f hf).hom.map_one
      map_mul' := by
        intro e₁ e₂
        apply h.isSeparatedFor.ext
        intro Y f hf
        change (sheaf R).obj.map f.op (a (e₁ * e₂)) =
          (sheaf R).obj.map f.op (mul R (.op X) (a e₁) (a e₂))
        rw [ha (e₁ * e₂) f hf, mapMul, ha e₁ f hf, ha e₂ f hf]
        exact (x f hf).hom.map_mul e₁ e₂
      map_zero' := by
        apply h.isSeparatedFor.ext
        intro Y f hf
        change (sheaf R).obj.map f.op (a 0) = (sheaf R).obj.map f.op (zero R (.op X))
        rw [ha 0 f hf, mapZero]
        exact (x f hf).hom.map_zero
      map_add' := by
        intro e₁ e₂
        apply h.isSeparatedFor.ext
        intro Y f hf
        change (sheaf R).obj.map f.op (a (e₁ + e₂)) =
          (sheaf R).obj.map f.op (add R (.op X) (a e₁) (a e₂))
        rw [ha (e₁ + e₂) f hf, mapAdd, ha e₁ f hf, ha e₂ f hf]
        exact (x f hf).hom.map_add e₁ e₂ }
  let gHom : E ⟶ obj R (.op X) :=
    @RingCat.ofHom E ((sheaf R).obj.obj (.op X)) (RingCat.ring E) (ring R (.op X)) g
  refine ⟨gHom, ?_, ?_⟩
  · intro Y f hf
    change gHom ≫ map R f.op = x f hf
    apply RingCat.hom_ext
    apply RingHom.ext
    intro e
    exact ha e f hf
  · intro g' hg'
    apply RingCat.hom_ext
    apply RingHom.ext
    intro e
    apply h.isSeparatedFor.ext
    intro Y f hf
    exact (congrArg (fun g : E ⟶ obj R (.op Y) ↦ g.hom e) (hg' f hf)).trans
      (ha e f hf).symm

end FromInternal

/-- Reconstruct a ring-valued sheaf from an internal ring in type-valued sheaves. -/
noncomputable def fromInternalObj (R : RingObjects J) : Sheaf J RingCat.{w} :=
  ⟨FromInternal.presheaf R, FromInternal.isSheaf R⟩

namespace FromInternal

variable {R S : RingObjects J} (f : RingObjects.Hom J R S)

/-- A morphism of internal rings preserves zero on every section type. -/
theorem homMapZero (U : Cᵒᵖ) :
    (RingObjects.hom J f).hom.app U (zero R U) = zero S U := by
  rcases f with ⟨φ⟩
  exact congrArg (fun g ↦ g.hom.app U PUnit.unit) (@IsAddMonHom.zero_hom _ _ _ _ _
    (data R).toAddGrpObj.toAddMonObj (data S).toAddGrpObj.toAddMonObj φ inferInstance)

/-- A morphism of internal rings preserves one on every section type. -/
theorem homMapOne (U : Cᵒᵖ) :
    (RingObjects.hom J f).hom.app U (one R U) = one S U := by
  rcases f with ⟨φ⟩
  exact congrArg (fun g ↦ g.hom.app U PUnit.unit) (@IsMonHom.one_hom _ _ _ _ _
    (data R).toMonObj (data S).toMonObj φ inferInstance)

/-- A morphism of internal rings preserves addition on every section type. -/
theorem homMapAdd (U : Cᵒᵖ) (x y : (sheaf R).obj.obj U) :
    (RingObjects.hom J f).hom.app U (add R U x y) =
      add S U ((RingObjects.hom J f).hom.app U x) ((RingObjects.hom J f).hom.app U y) := by
  rcases f with ⟨φ⟩
  exact congrArg (fun g ↦ g.hom.app U (x, y)) (@IsAddMonHom.add_hom _ _ _ _ _
    (data R).toAddGrpObj.toAddMonObj (data S).toAddGrpObj.toAddMonObj φ inferInstance)

/-- A morphism of internal rings preserves multiplication on every section type. -/
theorem homMapMul (U : Cᵒᵖ) (x y : (sheaf R).obj.obj U) :
    (RingObjects.hom J f).hom.app U (mul R U x y) =
      mul S U ((RingObjects.hom J f).hom.app U x) ((RingObjects.hom J f).hom.app U y) := by
  rcases f with ⟨φ⟩
  exact congrArg (fun g ↦ g.hom.app U (x, y)) (@IsMonHom.mul_hom _ _ _ _ _
    (data R).toMonObj (data S).toMonObj φ inferInstance)

/-- The ring homomorphism on sections induced by an internal-ring morphism. -/
noncomputable def homRingHom (U : Cᵒᵖ) : obj R U →+* obj S U where
  toFun := (RingObjects.hom J f).hom.app U
  map_one' := homMapOne f U
  map_mul' := homMapMul f U
  map_zero' := homMapZero f U
  map_add' := homMapAdd f U

/-- The component on sections of the reconstructed morphism of ring-valued presheaves. -/
noncomputable def homApp (U : Cᵒᵖ) : obj R U ⟶ obj S U :=
  @RingCat.ofHom ((sheaf R).obj.obj U) ((sheaf S).obj.obj U)
    (ring R U) (ring S U) (homRingHom f U)

/-- The reconstructed components of an internal-ring morphism are natural in the site object. -/
theorem homNaturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    map R g ≫ homApp f V = homApp f U ≫ map S g := by
  ext x
  exact congrArg (fun h ↦ h x) ((RingObjects.hom J f).hom.naturality g)

/-- The morphism of ring-valued presheaves reconstructed from an internal-ring morphism. -/
noncomputable def presheafMap : presheaf R ⟶ presheaf S where
  app := homApp f
  naturality := fun {_ _} g ↦ homNaturality f g

end FromInternal

/-- Reconstruct a morphism of ring-valued sheaves from an internal-ring morphism. -/
noncomputable def fromInternalMap {R S : RingObjects J} (f : RingObjects.Hom J R S) :
    fromInternalObj R ⟶ fromInternalObj S :=
  ObjectProperty.homMk (FromInternal.presheafMap f)

/-- Reconstruction from internal rings preserves identity morphisms. -/
theorem fromInternalMap_id (R : RingObjects J) :
    fromInternalMap (𝟙 R) = 𝟙 (fromInternalObj R) := by
  ext U x
  rfl

/-- Reconstruction from internal rings preserves composition. -/
theorem fromInternalMap_comp {R S T : RingObjects J}
    (f : RingObjects.Hom J R S) (g : RingObjects.Hom J S T) :
    fromInternalMap (RingObjects.comp J f g) = fromInternalMap f ≫ fromInternalMap g := by
  ext U x
  rfl

/-- The functor reconstructing ring-valued sheaves from internal ring objects. -/
noncomputable def fromInternal : RingObjects J ⥤ Sheaf J RingCat.{w} where
  obj := fromInternalObj
  map := fromInternalMap
  map_id := fromInternalMap_id
  map_comp := fromInternalMap_comp

section Comparison

variable [J.HasSheafCompose (forget RingCat.{w})]

/-- Forgetting coefficients after reconstructing a ring-valued sheaf recovers the underlying
type-valued sheaf of the internal ring. -/
noncomputable def fromInternalForgetIso :
    fromInternal ⋙ sheafCompose J (forget RingCat.{w}) ≅ RingObjects.forget J :=
  Iso.refl _

namespace Comparison

/-- The identity on the underlying sheaf is an internal-ring morphism from reconstruction followed
by forgetting back to the original internal ring. -/
theorem fromToHomIsRingHom (R : RingObjects J) :
    @IsRingHom (Sheaf J (Type w)) _ _ (underlying (fromInternalObj R)) (FromInternal.sheaf R)
      (addMonObj (fromInternalObj R)) (FromInternal.data R).toAddGrpObj.toAddMonObj
      (monObj (fromInternalObj R)) (FromInternal.data R).toMonObj
      (𝟙 (FromInternal.sheaf R)) := by
  refine @IsRingHom.mk (Sheaf J (Type w)) _ _ (underlying (fromInternalObj R)) (FromInternal.sheaf R)
    (addMonObj (fromInternalObj R)) (FromInternal.data R).toAddGrpObj.toAddMonObj
    (monObj (fromInternalObj R)) (FromInternal.data R).toMonObj _
    (@IsAddMonHom.mk (Sheaf J (Type w)) _ _ (underlying (fromInternalObj R)) (FromInternal.sheaf R)
      (addMonObj (fromInternalObj R)) (FromInternal.data R).toAddGrpObj.toAddMonObj _ ?_ ?_)
    (@IsMonHom.mk (Sheaf J (Type w)) _ _ (underlying (fromInternalObj R)) (FromInternal.sheaf R)
      (monObj (fromInternalObj R)) (FromInternal.data R).toMonObj _ ?_ ?_)
  · ext U x
    cases x
    rfl
  · ext U x
    rfl
  · ext U x
    cases x
    rfl
  · ext U x
    rfl

/-- The forward component of the comparison from reconstructed internal rings to the original
internal ring. -/
noncomputable def fromToHom (R : RingObjects J) :
    RingObjects.Hom J (toInternalObj (fromInternalObj R)) R :=
  @RingObjCat.Hom.mk (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)
    (toInternalObj (fromInternalObj R)) R (𝟙 (FromInternal.sheaf R))
    (fromToHomIsRingHom R)

/-- The identity on the underlying sheaf is an internal-ring morphism from the original internal
ring to reconstruction followed by forgetting. -/
theorem fromToInvIsRingHom (R : RingObjects J) :
    @IsRingHom (Sheaf J (Type w)) _ _ (FromInternal.sheaf R) (underlying (fromInternalObj R))
      (FromInternal.data R).toAddGrpObj.toAddMonObj (addMonObj (fromInternalObj R))
      (FromInternal.data R).toMonObj (monObj (fromInternalObj R))
      (𝟙 (FromInternal.sheaf R)) := by
  refine @IsRingHom.mk (Sheaf J (Type w)) _ _ (FromInternal.sheaf R) (underlying (fromInternalObj R))
    (FromInternal.data R).toAddGrpObj.toAddMonObj (addMonObj (fromInternalObj R))
    (FromInternal.data R).toMonObj (monObj (fromInternalObj R)) _
    (@IsAddMonHom.mk (Sheaf J (Type w)) _ _ (FromInternal.sheaf R) (underlying (fromInternalObj R))
      (FromInternal.data R).toAddGrpObj.toAddMonObj (addMonObj (fromInternalObj R)) _ ?_ ?_)
    (@IsMonHom.mk (Sheaf J (Type w)) _ _ (FromInternal.sheaf R) (underlying (fromInternalObj R))
      (FromInternal.data R).toMonObj (monObj (fromInternalObj R)) _ ?_ ?_)
  · ext U x
    cases x
    rfl
  · ext U x
    rfl
  · ext U x
    cases x
    rfl
  · ext U x
    rfl

/-- The inverse component of the comparison from reconstructed internal rings to the original
internal ring. -/
noncomputable def fromToInv (R : RingObjects J) :
    RingObjects.Hom J R (toInternalObj (fromInternalObj R)) :=
  @RingObjCat.Hom.mk (Sheaf J (Type w)) _ _ (sheafBraidedCategory J)
    R (toInternalObj (fromInternalObj R)) (𝟙 (FromInternal.sheaf R))
    (fromToInvIsRingHom R)

/-- The two directions of the internal-ring reconstruction comparison compose to the source
identity. -/
theorem fromToHomInvId (R : RingObjects J) :
    RingObjects.comp J (fromToHom R) (fromToInv R) = 𝟙 (toInternalObj (fromInternalObj R)) := by
  apply RingObjCat.Hom.ext
  exact Category.id_comp _

/-- The two directions of the internal-ring reconstruction comparison compose to the target
identity. -/
theorem fromToInvHomId (R : RingObjects J) :
    RingObjects.comp J (fromToInv R) (fromToHom R) = 𝟙 R := by
  apply RingObjCat.Hom.ext
  exact Category.id_comp _

/-- The component comparing an internal ring with reconstruction through ring-valued sheaves. -/
noncomputable def fromToAppIso (R : RingObjects J) :
    toInternalObj (fromInternalObj R) ≅ R where
  hom := fromToHom R
  inv := fromToInv R
  hom_inv_id := fromToHomInvId R
  inv_hom_id := fromToInvHomId R

/-- The internal-ring reconstruction comparison is natural. -/
theorem fromToNaturality {R S : RingObjects J} (f : RingObjects.Hom J R S) :
    (fromInternal ⋙ toInternal).map f ≫ (fromToAppIso S).hom =
      (fromToAppIso R).hom ≫ (𝟭 (RingObjects J)).map f := by
  apply RingObjCat.Hom.ext
  ext U x
  rfl

end Comparison

/-- Reconstructing a ring-valued sheaf and converting it back recovers the internal ring. -/
noncomputable def fromToIso : fromInternal ⋙ toInternal ≅ 𝟭 (RingObjects J) :=
  NatIso.ofComponents Comparison.fromToAppIso Comparison.fromToNaturality

namespace Comparison

variable (A : Sheaf J RingCat.{w}) (U : Cᵒᵖ)

/-- Reconstructing sections after passing to an internal ring preserves the original zero. -/
theorem toFromHomMapZero :
    FromInternal.zero (toInternalObj A) U = (0 : A.obj.obj U) := rfl

/-- Reconstructing sections after passing to an internal ring preserves the original one. -/
theorem toFromHomMapOne :
    FromInternal.one (toInternalObj A) U = (1 : A.obj.obj U) := rfl

/-- Reconstructing sections after passing to an internal ring preserves the original addition. -/
theorem toFromHomMapAdd (x y : A.obj.obj U) :
    FromInternal.add (toInternalObj A) U x y = x + y := rfl

/-- Reconstructing sections after passing to an internal ring preserves the original
multiplication. -/
theorem toFromHomMapMul (x y : A.obj.obj U) :
    FromInternal.mul (toInternalObj A) U x y = x * y := rfl

/-- The identity function from reconstructed sections to the original section ring. -/
noncomputable def toFromHomRingHom :
    FromInternal.obj (toInternalObj A) U →+* A.obj.obj U where
  toFun := fun x ↦ x
  map_one' := toFromHomMapOne A U
  map_mul' := toFromHomMapMul A U
  map_zero' := toFromHomMapZero A U
  map_add' := toFromHomMapAdd A U

/-- The identity function from the original section ring to reconstructed sections preserves
zero. -/
theorem toFromInvMapZero :
    (0 : A.obj.obj U) = FromInternal.zero (toInternalObj A) U := rfl

/-- The identity function from the original section ring to reconstructed sections preserves
one. -/
theorem toFromInvMapOne :
    (1 : A.obj.obj U) = FromInternal.one (toInternalObj A) U := rfl

/-- The identity function from the original section ring to reconstructed sections preserves
addition. -/
theorem toFromInvMapAdd (x y : A.obj.obj U) :
    x + y = FromInternal.add (toInternalObj A) U x y := rfl

/-- The identity function from the original section ring to reconstructed sections preserves
multiplication. -/
theorem toFromInvMapMul (x y : A.obj.obj U) :
    x * y = FromInternal.mul (toInternalObj A) U x y := rfl

/-- The identity ring homomorphism from the original section ring to reconstructed sections. -/
noncomputable def toFromInvRingHom :
    A.obj.obj U →+* FromInternal.obj (toInternalObj A) U where
  toFun := fun x ↦ x
  map_one' := toFromInvMapOne A U
  map_mul' := toFromInvMapMul A U
  map_zero' := toFromInvMapZero A U
  map_add' := toFromInvMapAdd A U

/-- The forward component on one site object of the ring-sheaf reconstruction comparison. -/
noncomputable def toFromHomApp :
    FromInternal.obj (toInternalObj A) U ⟶ A.obj.obj U :=
  @RingCat.ofHom ((FromInternal.sheaf (toInternalObj A)).obj.obj U) (A.obj.obj U)
    (FromInternal.ring (toInternalObj A) U) (RingCat.ring (A.obj.obj U))
    (toFromHomRingHom A U)

/-- The inverse component on one site object of the ring-sheaf reconstruction comparison. -/
noncomputable def toFromInvApp :
    A.obj.obj U ⟶ FromInternal.obj (toInternalObj A) U :=
  @RingCat.ofHom (A.obj.obj U) ((FromInternal.sheaf (toInternalObj A)).obj.obj U)
    (RingCat.ring (A.obj.obj U)) (FromInternal.ring (toInternalObj A) U)
    (toFromInvRingHom A U)

/-- The forward sectionwise components of the ring-sheaf reconstruction comparison are natural. -/
theorem toFromHomNaturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    FromInternal.map (toInternalObj A) f ≫ toFromHomApp A V =
      toFromHomApp A U ≫ A.obj.map f := by
  ext x
  rfl

/-- The inverse sectionwise components of the ring-sheaf reconstruction comparison are natural. -/
theorem toFromInvNaturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    A.obj.map f ≫ toFromInvApp A V =
      toFromInvApp A U ≫ FromInternal.map (toInternalObj A) f := by
  ext x
  rfl

/-- The forward morphism of ring-valued presheaves in the reconstruction comparison. -/
noncomputable def toFromHomPresheaf :
    FromInternal.presheaf (toInternalObj A) ⟶ A.obj where
  app := toFromHomApp A
  naturality := fun {_ _} f ↦ toFromHomNaturality A f

/-- The inverse morphism of ring-valued presheaves in the reconstruction comparison. -/
noncomputable def toFromInvPresheaf :
    A.obj ⟶ FromInternal.presheaf (toInternalObj A) where
  app := toFromInvApp A
  naturality := fun {_ _} f ↦ toFromInvNaturality A f

/-- The forward morphism of ring-valued sheaves in the reconstruction comparison. -/
noncomputable def toFromHom : fromInternalObj (toInternalObj A) ⟶ A :=
  ObjectProperty.homMk (toFromHomPresheaf A)

/-- The inverse morphism of ring-valued sheaves in the reconstruction comparison. -/
noncomputable def toFromInv : A ⟶ fromInternalObj (toInternalObj A) :=
  ObjectProperty.homMk (toFromInvPresheaf A)

/-- The two directions of the ring-sheaf reconstruction comparison compose to the source
identity. -/
theorem toFromHomInvId :
    toFromHom A ≫ toFromInv A = 𝟙 (fromInternalObj (toInternalObj A)) := by
  ext U x
  rfl

/-- The two directions of the ring-sheaf reconstruction comparison compose to the target
identity. -/
theorem toFromInvHomId : toFromInv A ≫ toFromHom A = 𝟙 A := by
  ext U x
  rfl

/-- The component comparing a ring-valued sheaf with reconstruction through internal rings. -/
noncomputable def toFromAppIso : fromInternalObj (toInternalObj A) ≅ A where
  hom := toFromHom A
  inv := toFromInv A
  hom_inv_id := toFromHomInvId A
  inv_hom_id := toFromInvHomId A

/-- The ring-valued-sheaf reconstruction comparison is natural. -/
theorem toFromNaturality {A B : Sheaf J RingCat.{w}} (f : A ⟶ B) :
    (toInternal ⋙ fromInternal).map f ≫ (toFromAppIso B).hom =
      (toFromAppIso A).hom ≫ (𝟭 (Sheaf J RingCat.{w})).map f := by
  ext U x
  rfl

end Comparison

/-- Converting a ring-valued sheaf to an internal ring and reconstructing it recovers the sheaf. -/
noncomputable def toFromIso : toInternal ⋙ fromInternal ≅ 𝟭 (Sheaf J RingCat.{w}) :=
  NatIso.ofComponents Comparison.toFromAppIso Comparison.toFromNaturality

/-- The two reconstruction comparisons satisfy the triangle identity on internal rings. -/
theorem equivalence_triangle (A : Sheaf J RingCat.{w}) :
    toInternal.map (toFromIso.inv.app A) ≫ fromToIso.hom.app (toInternal.obj A) =
      𝟙 (toInternal.obj A) := by
  apply RingObjCat.Hom.ext
  ext U x
  rfl

/-- Ring-valued sheaves are equivalent to internal ring objects in type-valued sheaves. -/
noncomputable def equivalence : Sheaf J RingCat.{w} ≌ RingObjects J where
  functor := toInternal
  inverse := fromInternal
  unitIso := toFromIso.symm
  counitIso := fromToIso
  functor_unitIso_comp := equivalence_triangle

end Comparison

-- Every carrier, operation, restriction map, functor component, and inverse component above is
-- explicit; no non-Prop payload is selected from an existence or `IsIso` proof.

end CategoryTheory.Sheaf.InternalRing
