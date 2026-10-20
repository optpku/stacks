/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Module.Internal
public import ReasLib.Algebra.Category.Ring.Sheaf.Internal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves of modules as internal module objects

For a ring-valued sheaf `R`, this module compares `SheafOfModules R` with left module objects
over the internal ring `InternalRing.toInternalObj R` in type-valued sheaves.  The side convention
agrees with `PresheafOfModules`: scalar actions have the form `R ⊗ M ⟶ M`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.AddMonObj CategoryTheory.MonObj

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.InternalModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [hRing : J.HasSheafCompose (forget RingCat.{w})]

/-- Internal left modules over the ring object associated to a ring-valued sheaf. -/
@[stacks 0FRE "internal modules over a ring-valued sheaf"]
abbrev ModuleObjects (R : Sheaf J RingCat.{w}) :=
  @ModuleObjCat (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R)

namespace ModuleObjects

/-- The underlying type-valued sheaf of an internal module. -/
abbrev carrier (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) : Sheaf J (Type w) :=
  @ModuleObjCat.X (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) M

/-- The internal left-module structure carried by an object of `ModuleObjects R`. -/
abbrev moduleObj (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    @ModuleObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (carrier R M) :=
  @ModuleObjCat.moduleObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) M

/-- Morphisms of internal modules, with the canonical sheaf braiding fixed. -/
abbrev Hom (R : Sheaf J RingCat.{w}) (M N : ModuleObjects R) :=
  @ModuleObjCat.Hom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) M N

/-- The underlying morphism of type-valued sheaves of an internal-module morphism. -/
abbrev hom (R : Sheaf J RingCat.{w}) {M N : ModuleObjects R} (f : Hom R M N) :
    carrier R M ⟶ carrier R N :=
  @ModuleObjCat.Hom.hom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) M N f

/-- The category structure on internal modules with the canonical sheaf braiding fixed. -/
noncomputable instance (priority := high) category (R : Sheaf J RingCat.{w}) :
    Category (ModuleObjects R) :=
  @ModuleObjCat.category (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R)

/-- Composition of morphisms of internal modules. -/
def comp (R : Sheaf J RingCat.{w}) {L M N : ModuleObjects R}
    (f : Hom R L M) (g : Hom R M N) : Hom R L N :=
  @ModuleObjCat.comp (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) L M N f g

/-- Forget an internal module to its underlying type-valued sheaf. -/
def forget (R : Sheaf J RingCat.{w}) : ModuleObjects R ⥤ Sheaf J (Type w) :=
  @ModuleObjCat.forget (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R)

end ModuleObjects

namespace ToInternal

variable (R : Sheaf J RingCat.{w})

/-- The additive-group-valued sheaf underlying a sheaf of `R`-modules. -/
abbrev addSheaf (M : SheafOfModules.{w} R) : Sheaf J AddCommGrpCat.{w} :=
  (SheafOfModules.toSheaf R).obj M

/-- The underlying restriction function of a sheaf of modules. -/
def restrictionApp (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (M.val.obj U : Type w) ⟶ (M.val.obj V : Type w) :=
  ↾fun x ↦ M.val.map f x

/-- Underlying restriction functions preserve identities. -/
theorem restrictionApp_id (M : SheafOfModules.{w} R) (U : Cᵒᵖ) :
    restrictionApp R M (𝟙 U) = 𝟙 (M.val.obj U : Type w) := sorry

/-- Underlying restriction functions preserve composition. -/
theorem restrictionApp_comp (M : SheafOfModules.{w} R) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    restrictionApp R M (f ≫ g) =
      (restrictionApp R M f : (M.val.obj U : Type w) ⟶ (M.val.obj V : Type w)) ≫
        (restrictionApp R M g : (M.val.obj V : Type w) ⟶ (M.val.obj W : Type w)) := sorry

/-- The ordinary presheaf of types underlying a sheaf of modules. -/
abbrev carrierPresheaf (M : SheafOfModules.{w} R) : Cᵒᵖ ⥤ Type w where
  obj U := M.val.obj U
  map := restrictionApp R M
  map_id := restrictionApp_id R M
  map_comp := restrictionApp_comp R M

/-- The ordinary underlying presheaf of types of a sheaf of `R`-modules is a sheaf. -/
theorem carrierIsSheaf (M : SheafOfModules.{w} R) :
    Presheaf.IsSheaf J (carrierPresheaf R M) := sorry

/-- The type-valued sheaf underlying a sheaf of `R`-modules. -/
noncomputable abbrev carrier (M : SheafOfModules.{w} R) : Sheaf J (Type w) :=
  ⟨carrierPresheaf R M, carrierIsSheaf R M⟩

/-- The internal ring carrier acting on an internalized sheaf of modules. -/
abbrev ringCarrier : Sheaf J (Type w) :=
  InternalRing.RingObjects.carrier J (InternalRing.toInternalObj R)

variable (M : SheafOfModules.{w} R) (U : Cᵒᵖ)

/-- The canonical identity comparison between an internalized carrier section and the original
module section. -/
abbrev sectionEquiv : (carrier R M).obj.obj U ≃ M.val.obj U := Equiv.refl _

/-- The canonical identity comparison between global sections of an internalized carrier and
global sections of the original module sheaf. -/
abbrev sectionsEquiv : (carrier R M).obj.sections ≃ M.sections := Equiv.refl _

/-- The canonical identity comparison between an internalized ring-carrier section and the
original ring section. -/
abbrev ringSectionEquiv : (ringCarrier R).obj.obj U ≃ R.obj.obj U := Equiv.refl _

/-- The zero section at one object of the site. -/
def zeroApp :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.obj U ⟶ (carrier R M).obj.obj U :=
  ↾fun _ ↦ (sectionEquiv R M U).symm (0 : M.val.obj U)

/-- Naturality of the zero sections. -/
theorem zeroApp_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (MonoidalCategory.tensorUnit (Sheaf J (Type w))).obj.map f ≫ zeroApp R M V =
      zeroApp R M U ≫ (carrier R M).obj.map f := sorry

/-- The zero operation on the internalized module. -/
def zero : 𝟙_ (Sheaf J (Type w)) ⟶ carrier R M :=
  ObjectProperty.homMk
    { app := zeroApp R M
      naturality := fun {_ _} f ↦ zeroApp_naturality R M f }

/-- Sectionwise addition at one object of the site. -/
def addApp : ((carrier R M) ⊗ (carrier R M)).obj.obj U ⟶ (carrier R M).obj.obj U :=
  ↾fun x ↦ (sectionEquiv R M U).symm
    (sectionEquiv R M U x.1 + sectionEquiv R M U x.2)

/-- Naturality of sectionwise addition. -/
theorem addApp_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((carrier R M) ⊗ (carrier R M)).obj.map f ≫ addApp R M V =
      addApp R M U ≫ (carrier R M).obj.map f := sorry

/-- Addition on the internalized module. -/
def add : carrier R M ⊗ carrier R M ⟶ carrier R M :=
  ObjectProperty.homMk
    { app := addApp R M
      naturality := fun {_ _} f ↦ addApp_naturality R M f }

/-- Sectionwise negation at one object of the site. -/
def negApp : (carrier R M).obj.obj U ⟶ (carrier R M).obj.obj U :=
  ↾fun x ↦ (sectionEquiv R M U).symm (-sectionEquiv R M U x)

/-- Naturality of sectionwise negation. -/
theorem negApp_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (carrier R M).obj.map f ≫ negApp R M V =
      negApp R M U ≫ (carrier R M).obj.map f := sorry

/-- Negation on the internalized module. -/
def neg : carrier R M ⟶ carrier R M :=
  ObjectProperty.homMk
    { app := negApp R M
      naturality := fun {_ _} f ↦ negApp_naturality R M f }

/-- The sectionwise left scalar action at one object of the site. -/
def smulApp : ((ringCarrier R) ⊗ (carrier R M)).obj.obj U ⟶ (carrier R M).obj.obj U :=
  ↾fun x ↦ (sectionEquiv R M U).symm
    (ringSectionEquiv R U x.1 • sectionEquiv R M U x.2)

/-- Naturality of the sectionwise left scalar action. -/
theorem smulApp_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((ringCarrier R) ⊗ (carrier R M)).obj.map f ≫ smulApp R M V =
      smulApp R M U ≫ (carrier R M).obj.map f := sorry

/-- The left action of the internal ring on the internalized module. -/
def smul : ringCarrier R ⊗ carrier R M ⟶ carrier R M :=
  ObjectProperty.homMk
    { app := smulApp R M
      naturality := fun {_ _} f ↦ smulApp_naturality R M f }

/-- Zero is a left identity for internal module addition. -/
theorem zero_add : zero R M ▷ carrier R M ≫ add R M = (λ_ (carrier R M)).hom := sorry

/-- Zero is a right identity for internal module addition. -/
theorem add_zero : carrier R M ◁ zero R M ≫ add R M = (ρ_ (carrier R M)).hom := sorry

/-- Internal module addition is associative. -/
theorem add_assoc :
    add R M ▷ carrier R M ≫ add R M =
      (α_ (carrier R M) (carrier R M) (carrier R M)).hom ≫
        carrier R M ◁ add R M ≫ add R M := sorry

/-- The additive-monoid structure of the internalized module. -/
@[implicit_reducible]
def addMonObj : AddMonObj (carrier R M) where
  zero := zero R M
  add := add R M
  zero_add := zero_add R M
  add_zero := add_zero R M
  add_assoc := add_assoc R M

/-- Negation is a left additive inverse on the internalized module. -/
theorem neg_add :
    lift (neg R M) (𝟙 (carrier R M)) ≫ add R M =
      toUnit (carrier R M) ≫ zero R M := sorry

/-- Negation is a right additive inverse on the internalized module. -/
theorem add_neg :
    lift (𝟙 (carrier R M)) (neg R M) ≫ add R M =
      toUnit (carrier R M) ≫ zero R M := sorry

/-- The additive-group structure of the internalized module. -/
@[implicit_reducible]
def addGrpObj : AddGrpObj (carrier R M) where
  toAddMonObj := addMonObj R M
  neg := neg R M
  left_neg := neg_add R M
  right_neg := add_neg R M

/-- The internalized additive group is commutative. -/
theorem isCommAddMonObj :
    @IsCommAddMonObj (Sheaf J (Type w)) _ _ _ (carrier R M) (addMonObj R M) := sorry

/-- The internal scalar action is unital. -/
theorem one_smul :
    (InternalRing.monObj R).one ▷ carrier R M ≫ smul R M =
      (λ_ (carrier R M)).hom := sorry

/-- The internal scalar action is associative. -/
theorem mul_smul :
    (InternalRing.monObj R).mul ▷ carrier R M ≫ smul R M =
      (α_ (ringCarrier R) (ringCarrier R) (carrier R M)).hom ≫
        ringCarrier R ◁ smul R M ≫ smul R M := sorry

/-- Addition of internal scalars distributes over the action. -/
theorem add_smul :
    InternalRing.add R ▷ carrier R M ≫ smul R M =
      lift (fst (ringCarrier R) (ringCarrier R) ▷ carrier R M ≫ smul R M)
          (snd (ringCarrier R) (ringCarrier R) ▷ carrier R M ≫ smul R M) ≫
        add R M := sorry

/-- The internal scalar action distributes over module addition. -/
theorem smul_add :
    ringCarrier R ◁ add R M ≫ smul R M =
      lift ((ringCarrier R ◁ fst (carrier R M) (carrier R M)) ≫ smul R M)
          ((ringCarrier R ◁ snd (carrier R M) (carrier R M)) ≫ smul R M) ≫
        add R M := sorry

/-- The internal left-module structure associated to a sheaf of modules. -/
@[implicit_reducible]
noncomputable def moduleObj :
    @ModuleObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (carrier R M) :=
  @ModuleObj.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) (carrier R M) (addGrpObj R M) (isCommAddMonObj R M)
    (@ModObj.mk (Sheaf J (Type w)) _ _ (Sheaf J (Type w)) _ _ (ringCarrier R)
      (InternalRing.monObj R) (carrier R M) (smul R M) (one_smul R M) (mul_smul R M))
    (add_smul R M) (smul_add R M)

/-- The component on underlying types of a morphism of sheaves of modules. -/
def carrierMapApp {M N : SheafOfModules.{w} R} (f : M ⟶ N) (U : Cᵒᵖ) :
    (carrier R M).obj.obj U ⟶ (carrier R N).obj.obj U :=
  ↾fun x ↦ (sectionEquiv R N U).symm (f.val.app U (sectionEquiv R M U x))

/-- The underlying components of a morphism of sheaves of modules are natural. -/
theorem carrierMapApp_naturality {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    {U V : Cᵒᵖ} (g : U ⟶ V) :
    (carrier R M).obj.map g ≫ carrierMapApp R f V =
      carrierMapApp R f U ≫ (carrier R N).obj.map g := sorry

/-- The underlying type-valued sheaf map induced by a morphism of sheaves of modules. -/
def carrierMap {M N : SheafOfModules.{w} R} (f : M ⟶ N) : carrier R M ⟶ carrier R N :=
  ObjectProperty.homMk
    { app := carrierMapApp R f
      naturality := fun {_ _} g ↦ carrierMapApp_naturality R f g }

/-- The underlying type-valued sheaf construction preserves identity morphisms. -/
theorem carrierMap_id (M : SheafOfModules.{w} R) : carrierMap R (𝟙 M) = 𝟙 (carrier R M) := sorry

/-- The underlying type-valued sheaf construction preserves composition. -/
theorem carrierMap_comp {L M N : SheafOfModules.{w} R} (f : L ⟶ M) (g : M ⟶ N) :
    carrierMap R (f ≫ g) = carrierMap R f ≫ carrierMap R g := sorry

/-- Forget a sheaf of modules to its underlying type-valued sheaf. -/
noncomputable def underlying : SheafOfModules.{w} R ⥤ Sheaf J (Type w) where
  obj := carrier R
  map := carrierMap R
  map_id := carrierMap_id R
  map_comp := carrierMap_comp R

end ToInternal

/-- Convert a sheaf of left `R`-modules to an internal module over `toInternalObj R`. -/
@[stacks 0FRE "internalization of a sheaf of modules"]
noncomputable def toInternalObj (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) :
    ModuleObjects R :=
  @ModuleObjCat.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) (ToInternal.carrier R M) (ToInternal.moduleObj R M)

/-- A morphism of sheaves of modules preserves the internal additive and scalar structures. -/
theorem toInternal_isModuleHom (R : Sheaf J RingCat.{w})
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) :
    @IsModuleHom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (ToInternal.carrier R M) (ToInternal.carrier R N)
      (ToInternal.moduleObj R M) (ToInternal.moduleObj R N) (ToInternal.carrierMap R f) := sorry

/-- Convert a morphism of sheaves of modules to an internal-module morphism. -/
noncomputable def toInternalMap (R : Sheaf J RingCat.{w})
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) :
    ModuleObjects.Hom R (toInternalObj R M) (toInternalObj R N) :=
  @ModuleObjCat.Hom.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) (toInternalObj R M) (toInternalObj R N)
    (ToInternal.carrierMap R f) (toInternal_isModuleHom R f)

/-- Conversion to internal modules preserves identity morphisms. -/
theorem toInternalMap_id (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) :
    toInternalMap R (𝟙 M) = 𝟙 (toInternalObj R M) := sorry

/-- Conversion to internal modules preserves composition. -/
theorem toInternalMap_comp (R : Sheaf J RingCat.{w}) {L M N : SheafOfModules.{w} R}
    (f : L ⟶ M) (g : M ⟶ N) :
    toInternalMap R (f ≫ g) = ModuleObjects.comp R (toInternalMap R f) (toInternalMap R g) := sorry

/-- The functor from sheaves of left modules to internal left-module objects. -/
@[stacks 0FRE "sheaves of modules as internal module objects"]
noncomputable def toInternal (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ⥤ ModuleObjects R where
  obj := toInternalObj R
  map := toInternalMap R
  map_id := toInternalMap_id R
  map_comp := toInternalMap_comp R

/-- Forgetting the internal module structure after `toInternal` recovers the ordinary
type-valued sheaf underlying a sheaf of modules. -/
noncomputable def toInternalForgetIso (R : Sheaf J RingCat.{w}) :
    toInternal R ⋙ ModuleObjects.forget R ≅ ToInternal.underlying R :=
  Iso.refl _

namespace FromInternal

variable (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) (U : Cᵒᵖ)

/-- The underlying sheaf of an internal module. -/
abbrev sheaf : Sheaf J (Type w) := ModuleObjects.carrier R M

/-- The internal module structure, accessed with the canonical sheaf braiding fixed. -/
abbrev data :
    @ModuleObj (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (sheaf R M) :=
  ModuleObjects.moduleObj R M

/-- The zero element on a section type of an internal module. -/
def zero : (sheaf R M).obj.obj U :=
  (data R M).toAddGrpObj.toAddMonObj.zero.hom.app U PUnit.unit

/-- Addition on a section type of an internal module. -/
def add (x y : (sheaf R M).obj.obj U) : (sheaf R M).obj.obj U :=
  (data R M).toAddGrpObj.toAddMonObj.add.hom.app U (x, y)

/-- Negation on a section type of an internal module. -/
def neg (x : (sheaf R M).obj.obj U) : (sheaf R M).obj.obj U :=
  (data R M).toAddGrpObj.neg.hom.app U x

/-- Scalar multiplication on a section type of an internal module. -/
def smul (r : R.obj.obj U) (x : (sheaf R M).obj.obj U) : (sheaf R M).obj.obj U :=
  (data R M).toModObj.smul.hom.app U ((ToInternal.ringSectionEquiv R U).symm r, x)

/-- The explicit addition operation used to reconstruct a section module. -/
@[implicit_reducible]
def addData : Add ((sheaf R M).obj.obj U) := ⟨add R M U⟩

/-- The explicit negation operation used to reconstruct a section module. -/
@[implicit_reducible]
def negData : Neg ((sheaf R M).obj.obj U) := ⟨neg R M U⟩

/-- The explicit zero used to reconstruct a section module. -/
@[implicit_reducible]
def zeroData : Zero ((sheaf R M).obj.obj U) := ⟨zero R M U⟩

/-- The explicit scalar action used to reconstruct a section module. -/
@[implicit_reducible]
def smulData : SMul (R.obj.obj U) ((sheaf R M).obj.obj U) := ⟨smul R M U⟩

/-- Reconstructed sectionwise addition is associative. -/
theorem addAssoc (a b c : (sheaf R M).obj.obj U) :
    add R M U (add R M U a b) c = add R M U a (add R M U b c) := sorry

/-- Reconstructed zero is a left additive identity. -/
theorem zeroAdd (a : (sheaf R M).obj.obj U) : add R M U (zero R M U) a = a := sorry

/-- Reconstructed negation is a left additive inverse. -/
theorem negAddCancel (a : (sheaf R M).obj.obj U) :
    add R M U (neg R M U a) a = zero R M U := sorry

/-- Reconstructed sectionwise addition is commutative. -/
theorem addComm (a b : (sheaf R M).obj.obj U) : add R M U a b = add R M U b a := sorry

/-- The additive commutative group reconstructed on a section of an internal module. -/
@[implicit_reducible]
noncomputable def addCommGroup : AddCommGroup ((sheaf R M).obj.obj U) :=
  { @AddGroup.ofLeftAxioms ((sheaf R M).obj.obj U) (addData R M U) (negData R M U)
      (zeroData R M U) (addAssoc R M U) (zeroAdd R M U) (negAddCancel R M U) with
    add_comm := addComm R M U }

/-- Reconstructed scalar multiplication distributes over module addition. -/
theorem smulAdd (r : R.obj.obj U) (x y : (sheaf R M).obj.obj U) :
    smul R M U r (add R M U x y) = add R M U (smul R M U r x) (smul R M U r y) := sorry

/-- Reconstructed addition of scalars distributes over scalar multiplication. -/
theorem addSmul (r s : R.obj.obj U) (x : (sheaf R M).obj.obj U) :
    smul R M U (r + s) x = add R M U (smul R M U r x) (smul R M U s x) := sorry

/-- Reconstructed scalar multiplication is associative. -/
theorem mulSmul (r s : R.obj.obj U) (x : (sheaf R M).obj.obj U) :
    smul R M U (r * s) x = smul R M U r (smul R M U s x) := sorry

/-- Reconstructed scalar multiplication is unital. -/
theorem oneSmul (x : (sheaf R M).obj.obj U) : smul R M U 1 x = x := sorry

/-- The module structure reconstructed on a section of an internal module. -/
@[implicit_reducible]
noncomputable def module :
    @Module (R.obj.obj U) ((sheaf R M).obj.obj U) _ (addCommGroup R M U).toAddCommMonoid :=
  @Module.ofMinimalAxioms (R.obj.obj U) ((sheaf R M).obj.obj U) _ (addCommGroup R M U)
    (smulData R M U) (smulAdd R M U) (addSmul R M U) (mulSmul R M U) (oneSmul R M U)

/-- The bundled module reconstructed on one section type of an internal module. -/
noncomputable def obj : ModuleCat.{w} (R.obj.obj U) :=
  @ModuleCat.of (R.obj.obj U) _ ((sheaf R M).obj.obj U) (addCommGroup R M U)
    (module R M U)

variable {U} {V : Cᵒᵖ}

/-- Restrictions preserve reconstructed sectionwise addition. -/
theorem mapAdd (f : U ⟶ V) (x y : (sheaf R M).obj.obj U) :
    (sheaf R M).obj.map f (add R M U x y) =
      add R M V ((sheaf R M).obj.map f x) ((sheaf R M).obj.map f y) := sorry

/-- Restrictions commute with the reconstructed semilinear scalar action. -/
theorem mapSmul (f : U ⟶ V) (r : R.obj.obj U) (x : (sheaf R M).obj.obj U) :
    (sheaf R M).obj.map f (smul R M U r x) =
      smul R M V (R.obj.map f r) ((sheaf R M).obj.map f x) := sorry

/-- The semilinear restriction map between reconstructed section modules. -/
noncomputable def mapLinearMap (f : U ⟶ V) :
    obj R M U →ₗ[R.obj.obj U]
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj (obj R M V) where
  toFun := (sheaf R M).obj.map f
  map_add' := mapAdd R M f
  map_smul' := mapSmul R M f

/-- The bundled restriction morphism between reconstructed section modules. -/
noncomputable def map (f : U ⟶ V) :
    obj R M U ⟶ (ModuleCat.restrictScalars (R.obj.map f).hom).obj (obj R M V) :=
  ConcreteCategory.ofHom (C := ModuleCat (R.obj.obj U)) (mapLinearMap R M f)

/-- Reconstructed module restrictions preserve identities. -/
theorem mapId (U : Cᵒᵖ) :
    map R M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (R.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id U))).inv.app _ := sorry

/-- Reconstructed module restrictions preserve composition. -/
theorem mapComp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    map R M (f ≫ g) = map R M f ≫
      (ModuleCat.restrictScalars (R.obj.map f).hom).map (map R M g) ≫
      (ModuleCat.restrictScalarsComp' (R.obj.map f).hom (R.obj.map g).hom
        (R.obj.map (f ≫ g)).hom (congrArg RingCat.Hom.hom (R.obj.map_comp f g))).inv.app _ := sorry

/-- The presheaf of modules reconstructed from an internal module. -/
noncomputable def presheaf : PresheafOfModules.{w} R.obj where
  obj := obj R M
  map := map R M
  map_id := mapId R M
  map_comp := mapComp R M

/-- The reconstructed presheaf of modules satisfies the sheaf condition. -/
theorem isSheaf : Presheaf.IsSheaf J (presheaf R M).presheaf := sorry

end FromInternal

/-- Reconstruct a sheaf of modules from an internal module. -/
@[stacks 0FRE "reconstruction of a sheaf of modules"]
noncomputable def fromInternalObj (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    SheafOfModules.{w} R :=
  ⟨FromInternal.presheaf R M, FromInternal.isSheaf R M⟩

namespace FromInternal

variable {R : Sheaf J RingCat.{w}} {M N : ModuleObjects R}
variable (f : ModuleObjects.Hom R M N)

/-- An internal-module morphism preserves reconstructed addition on every section. -/
theorem homMapAdd (U : Cᵒᵖ) (x y : (sheaf R M).obj.obj U) :
    (ModuleObjects.hom R f).hom.app U (add R M U x y) =
      add R N U ((ModuleObjects.hom R f).hom.app U x)
        ((ModuleObjects.hom R f).hom.app U y) := sorry

/-- An internal-module morphism preserves reconstructed scalar multiplication on every section. -/
theorem homMapSmul (U : Cᵒᵖ) (r : R.obj.obj U) (x : (sheaf R M).obj.obj U) :
    (ModuleObjects.hom R f).hom.app U (smul R M U r x) =
      smul R N U r ((ModuleObjects.hom R f).hom.app U x) := sorry

/-- The linear map on sections induced by an internal-module morphism. -/
noncomputable def homLinearMap (U : Cᵒᵖ) : obj R M U →ₗ[R.obj.obj U] obj R N U where
  toFun := (ModuleObjects.hom R f).hom.app U
  map_add' := homMapAdd f U
  map_smul' := homMapSmul f U

/-- The component on section modules of a reconstructed internal-module morphism. -/
noncomputable def homApp (U : Cᵒᵖ) : obj R M U ⟶ obj R N U :=
  ConcreteCategory.ofHom (C := ModuleCat (R.obj.obj U)) (homLinearMap f U)

/-- Reconstructed components of an internal-module morphism are natural in the site object. -/
theorem homNaturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    map R M g ≫ (ModuleCat.restrictScalars (R.obj.map g).hom).map (homApp f V) =
      homApp f U ≫ map R N g := sorry

/-- The morphism of module presheaves reconstructed from an internal-module morphism. -/
noncomputable def presheafMap : presheaf R M ⟶ presheaf R N where
  app := homApp f
  naturality := fun {_ _} g ↦ homNaturality f g

end FromInternal

/-- Reconstruct a morphism of sheaves of modules from an internal-module morphism. -/
noncomputable def fromInternalMap (R : Sheaf J RingCat.{w}) {M N : ModuleObjects R}
    (f : ModuleObjects.Hom R M N) : fromInternalObj R M ⟶ fromInternalObj R N :=
  ⟨FromInternal.presheafMap f⟩

/-- Reconstruction from internal modules preserves identity morphisms. -/
theorem fromInternalMap_id (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    fromInternalMap R (𝟙 M) = 𝟙 (fromInternalObj R M) := sorry

/-- Reconstruction from internal modules preserves composition. -/
theorem fromInternalMap_comp (R : Sheaf J RingCat.{w}) {L M N : ModuleObjects R}
    (f : ModuleObjects.Hom R L M) (g : ModuleObjects.Hom R M N) :
    fromInternalMap R (ModuleObjects.comp R f g) =
      fromInternalMap R f ≫ fromInternalMap R g := sorry

/-- The functor reconstructing sheaves of modules from internal module objects. -/
@[stacks 0FRE "internal module objects as sheaves of modules"]
noncomputable def fromInternal (R : Sheaf J RingCat.{w}) :
    ModuleObjects R ⥤ SheafOfModules.{w} R where
  obj := fromInternalObj R
  map := fromInternalMap R
  map_id := fromInternalMap_id R
  map_comp := fromInternalMap_comp R

namespace Comparison

/-- The identity on the underlying sheaf is module-linear from reconstruction followed by
internalization to the original internal module. -/
theorem fromToHomIsModuleHom (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    @IsModuleHom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (ToInternal.carrier R (fromInternalObj R M))
      (FromInternal.sheaf R M) (ToInternal.moduleObj R (fromInternalObj R M))
      (FromInternal.data R M) (𝟙 (FromInternal.sheaf R M)) := sorry

/-- The forward component comparing an internal module with reconstruction through sheaves of
modules. -/
noncomputable def fromToHom (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    ModuleObjects.Hom R (toInternalObj R (fromInternalObj R M)) M :=
  @ModuleObjCat.Hom.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) (toInternalObj R (fromInternalObj R M)) M
    (𝟙 (FromInternal.sheaf R M)) (fromToHomIsModuleHom R M)

/-- The identity on the underlying sheaf is module-linear from the original internal module to
reconstruction followed by internalization. -/
theorem fromToInvIsModuleHom (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    @IsModuleHom (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
      (InternalRing.toInternalObj R) (FromInternal.sheaf R M)
      (ToInternal.carrier R (fromInternalObj R M)) (FromInternal.data R M)
      (ToInternal.moduleObj R (fromInternalObj R M)) (𝟙 (FromInternal.sheaf R M)) := sorry

/-- The inverse component comparing an internal module with reconstruction through sheaves of
modules. -/
noncomputable def fromToInv (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    ModuleObjects.Hom R M (toInternalObj R (fromInternalObj R M)) :=
  @ModuleObjCat.Hom.mk (Sheaf J (Type w)) _ _ (InternalRing.sheafBraidedCategory J)
    (InternalRing.toInternalObj R) M (toInternalObj R (fromInternalObj R M))
    (𝟙 (FromInternal.sheaf R M)) (fromToInvIsModuleHom R M)

/-- The two internal-module comparison directions compose to the reconstructed identity. -/
theorem fromToHomInvId (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    ModuleObjects.comp R (fromToHom R M) (fromToInv R M) =
      𝟙 (toInternalObj R (fromInternalObj R M)) := sorry

/-- The two internal-module comparison directions compose to the original identity. -/
theorem fromToInvHomId (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    ModuleObjects.comp R (fromToInv R M) (fromToHom R M) = 𝟙 M := sorry

/-- The component comparing an internal module with reconstruction through sheaves of modules. -/
noncomputable def fromToAppIso (R : Sheaf J RingCat.{w}) (M : ModuleObjects R) :
    toInternalObj R (fromInternalObj R M) ≅ M where
  hom := fromToHom R M
  inv := fromToInv R M
  hom_inv_id := fromToHomInvId R M
  inv_hom_id := fromToInvHomId R M

/-- The internal-module reconstruction comparison is natural. -/
theorem fromToNaturality (R : Sheaf J RingCat.{w}) {M N : ModuleObjects R}
    (f : ModuleObjects.Hom R M N) :
    (fromInternal R ⋙ toInternal R).map f ≫ (fromToAppIso R N).hom =
      (fromToAppIso R M).hom ≫ (𝟭 (ModuleObjects R)).map f := sorry

end Comparison

/-- Reconstructing a sheaf of modules and internalizing it recovers the internal module. -/
@[stacks 0FRE "internal-module reconstruction comparison"]
noncomputable def fromToIso (R : Sheaf J RingCat.{w}) :
    fromInternal R ⋙ toInternal R ≅ 𝟭 (ModuleObjects R) :=
  NatIso.ofComponents (Comparison.fromToAppIso R) (Comparison.fromToNaturality R)

namespace Comparison

variable (R : Sheaf J RingCat.{w}) (A : SheafOfModules.{w} R) (U : Cᵒᵖ)

/-- Reconstructing after internalization preserves sectionwise addition. -/
theorem toFromHomMapAdd (x y : (FromInternal.sheaf R (toInternalObj R A)).obj.obj U) :
    ToInternal.sectionEquiv R A U
        (FromInternal.add R (toInternalObj R A) U x y) =
      ToInternal.sectionEquiv R A U x + ToInternal.sectionEquiv R A U y := sorry

/-- Reconstructing after internalization preserves sectionwise scalar multiplication. -/
theorem toFromHomMapSmul (r : R.obj.obj U)
    (x : (FromInternal.sheaf R (toInternalObj R A)).obj.obj U) :
    ToInternal.sectionEquiv R A U
        (FromInternal.smul R (toInternalObj R A) U r x) =
      r • ToInternal.sectionEquiv R A U x := sorry

/-- The identity linear map from reconstructed sections to the original section module. -/
noncomputable def toFromHomLinearMap :
    FromInternal.obj R (toInternalObj R A) U →ₗ[R.obj.obj U] A.val.obj U where
  toFun := ToInternal.sectionEquiv R A U
  map_add' := toFromHomMapAdd R A U
  map_smul' := toFromHomMapSmul R A U

/-- The inverse identity function preserves reconstructed sectionwise addition. -/
theorem toFromInvMapAdd (x y : A.val.obj U) :
    (ToInternal.sectionEquiv R A U).symm (x + y) =
      FromInternal.add R (toInternalObj R A) U
        ((ToInternal.sectionEquiv R A U).symm x)
        ((ToInternal.sectionEquiv R A U).symm y) := sorry

/-- The inverse identity function preserves reconstructed scalar multiplication. -/
theorem toFromInvMapSmul (r : R.obj.obj U) (x : A.val.obj U) :
    (ToInternal.sectionEquiv R A U).symm (r • x) =
      FromInternal.smul R (toInternalObj R A) U r
        ((ToInternal.sectionEquiv R A U).symm x) := sorry

/-- The identity linear map from the original section module to reconstructed sections. -/
noncomputable def toFromInvLinearMap :
    A.val.obj U →ₗ[R.obj.obj U] FromInternal.obj R (toInternalObj R A) U where
  toFun := (ToInternal.sectionEquiv R A U).symm
  map_add' := toFromInvMapAdd R A U
  map_smul' := toFromInvMapSmul R A U

/-- The forward component on one site object of the module-sheaf reconstruction comparison. -/
noncomputable def toFromHomApp :
    FromInternal.obj R (toInternalObj R A) U ⟶ A.val.obj U :=
  ConcreteCategory.ofHom (C := ModuleCat (R.obj.obj U)) (toFromHomLinearMap R A U)

/-- The inverse component on one site object of the module-sheaf reconstruction comparison. -/
noncomputable def toFromInvApp :
    A.val.obj U ⟶ FromInternal.obj R (toInternalObj R A) U :=
  ConcreteCategory.ofHom (C := ModuleCat (R.obj.obj U)) (toFromInvLinearMap R A U)

/-- The forward sectionwise components of the module-sheaf comparison are natural. -/
theorem toFromHomNaturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    FromInternal.map R (toInternalObj R A) f ≫
        (ModuleCat.restrictScalars (R.obj.map f).hom).map (toFromHomApp R A V) =
      toFromHomApp R A U ≫ A.val.map f := sorry

/-- The inverse sectionwise components of the module-sheaf comparison are natural. -/
theorem toFromInvNaturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    A.val.map f ≫
        (ModuleCat.restrictScalars (R.obj.map f).hom).map (toFromInvApp R A V) =
      toFromInvApp R A U ≫ FromInternal.map R (toInternalObj R A) f := sorry

/-- The forward morphism of module presheaves in the reconstruction comparison. -/
noncomputable def toFromHomPresheaf :
    FromInternal.presheaf R (toInternalObj R A) ⟶ A.val where
  app := toFromHomApp R A
  naturality := fun {_ _} f ↦ toFromHomNaturality R A f

/-- The inverse morphism of module presheaves in the reconstruction comparison. -/
noncomputable def toFromInvPresheaf :
    A.val ⟶ FromInternal.presheaf R (toInternalObj R A) where
  app := toFromInvApp R A
  naturality := fun {_ _} f ↦ toFromInvNaturality R A f

/-- The forward morphism of sheaves of modules in the reconstruction comparison. -/
noncomputable def toFromHom : fromInternalObj R (toInternalObj R A) ⟶ A :=
  ⟨toFromHomPresheaf R A⟩

/-- The inverse morphism of sheaves of modules in the reconstruction comparison. -/
noncomputable def toFromInv : A ⟶ fromInternalObj R (toInternalObj R A) :=
  ⟨toFromInvPresheaf R A⟩

/-- The two module-sheaf comparison directions compose to the reconstructed identity. -/
theorem toFromHomInvId :
    toFromHom R A ≫ toFromInv R A = 𝟙 (fromInternalObj R (toInternalObj R A)) := sorry

/-- The two module-sheaf comparison directions compose to the original identity. -/
theorem toFromInvHomId : toFromInv R A ≫ toFromHom R A = 𝟙 A := sorry

/-- The component comparing a sheaf of modules with reconstruction through internal modules. -/
noncomputable def toFromAppIso : fromInternalObj R (toInternalObj R A) ≅ A where
  hom := toFromHom R A
  inv := toFromInv R A
  hom_inv_id := toFromHomInvId R A
  inv_hom_id := toFromInvHomId R A

/-- The module-sheaf reconstruction comparison is natural. -/
theorem toFromNaturality {A B : SheafOfModules.{w} R} (f : A ⟶ B) :
    (toInternal R ⋙ fromInternal R).map f ≫ (toFromAppIso R B).hom =
      (toFromAppIso R A).hom ≫ (𝟭 (SheafOfModules.{w} R)).map f := sorry

end Comparison

/-- Internalizing a sheaf of modules and reconstructing it recovers the original sheaf. -/
@[stacks 0FRE "module-sheaf reconstruction comparison"]
noncomputable def toFromIso (R : Sheaf J RingCat.{w}) :
    toInternal R ⋙ fromInternal R ≅ 𝟭 (SheafOfModules.{w} R) :=
  NatIso.ofComponents (Comparison.toFromAppIso R) (Comparison.toFromNaturality R)

/-- The two reconstruction comparisons satisfy the triangle identity on internal modules. -/
theorem equivalence_triangle (R : Sheaf J RingCat.{w}) (A : SheafOfModules.{w} R) :
    (toInternal R).map ((toFromIso R).inv.app A) ≫
        (fromToIso R).hom.app ((toInternal R).obj A) =
      𝟙 ((toInternal R).obj A) := sorry

/-- Sheaves of left modules are equivalent to internal left modules over the associated internal
ring in type-valued sheaves. -/
@[stacks 0FRE "sheaves of modules as internal module objects"]
noncomputable def equivalence (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ≌ ModuleObjects R where
  functor := toInternal R
  inverse := fromInternal R
  unitIso := (toFromIso R).symm
  counitIso := fromToIso R
  functor_unitIso_comp := equivalence_triangle R

end CategoryTheory.Sheaf.InternalModule
