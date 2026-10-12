/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Internal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Internal modules over internal ring objects

This module defines left modules over ring objects in a braided cartesian monoidal category,
their morphisms and bundled category, and their functorial image under braided monoidal functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.AddMonObj CategoryTheory.MonObj

noncomputable section

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- A left module object over an internal ring `R` consists of a commutative additive-group
object, a left action of the multiplicative monoid of `R`, and the two distributivity laws. -/
class ModuleObj (R : RingObjCat C) (M : C)
    extends AddGrpObj M, IsCommAddMonObj M, ModObj R.X M where
  /-- Addition of scalars distributes over the action. -/
  add_smul (M) :
    σ[R.X] ▷ M ≫ γ[R.X, M] =
      lift (fst R.X R.X ▷ M ≫ γ[R.X, M])
          (snd R.X R.X ▷ M ≫ γ[R.X, M]) ≫
        σ[M]
  /-- The action of a scalar distributes over addition in the module. -/
  smul_add (M) :
    R.X ◁ σ[M] ≫ γ[R.X, M] =
      lift ((R.X ◁ fst M M) ≫ γ[R.X, M])
          ((R.X ◁ snd M M) ≫ γ[R.X, M]) ≫
        σ[M]

/-- A morphism of internal `R`-modules is both additive and compatible with the left action. -/
class IsModuleHom (R : RingObjCat C) {M N : C}
    [ModuleObj R M] [ModuleObj R N] (f : M ⟶ N) : Prop
    extends IsAddMonHom f, IsModHom R.X f

namespace IsModuleHom

/-- Identity morphisms preserve the internal module structure. -/
theorem id (R : RingObjCat C) (M : C) [ModuleObj R M] :
    IsModuleHom R (𝟙 M) := sorry

/-- Composites of internal module morphisms preserve the internal module structure. -/
theorem comp (R : RingObjCat C) {M N P : C}
    [ModuleObj R M] [ModuleObj R N] [ModuleObj R P]
    (f : M ⟶ N) (g : N ⟶ P) [IsModuleHom R f] [IsModuleHom R g] :
    IsModuleHom R (f ≫ g) := sorry

attribute [instance] id comp

end IsModuleHom

/-- The bundled category of left module objects over an internal ring `R`. -/
abbrev ModuleObjCat (R : RingObjCat C) := Σ X : C, ModuleObj R X

namespace ModuleObjCat

/-- Construct a bundled internal module from its carrier and module structure. -/
def mk {R : RingObjCat C} (X : C) (moduleObj : ModuleObj R X) : ModuleObjCat R :=
  ⟨X, moduleObj⟩

/-- The carrier of a bundled internal module. -/
abbrev X {R : RingObjCat C} (M : ModuleObjCat R) : C := M.1

/-- The internal module structure carried by a bundled internal module. -/
abbrev moduleObj {R : RingObjCat C} (M : ModuleObjCat R) : ModuleObj R M.X := M.2

/-- A bundled morphism of internal left modules. -/
abbrev Hom {R : RingObjCat C} (M N : ModuleObjCat R) :=
  {f : M.X ⟶ N.X //
    @IsModuleHom C _ _ _ R M.X N.X M.moduleObj N.moduleObj f}

namespace Hom

/-- Construct a bundled internal-module morphism from its map and preservation proof. -/
def mk {R : RingObjCat C} {M N : ModuleObjCat R} (hom : M.X ⟶ N.X)
    (isModuleHom : @IsModuleHom C _ _ _ R M.X N.X M.moduleObj N.moduleObj hom) : Hom M N :=
  ⟨hom, isModuleHom⟩

/-- The underlying morphism of a bundled internal-module morphism. -/
abbrev hom {R : RingObjCat C} {M N : ModuleObjCat R} (f : Hom M N) : M.X ⟶ N.X := f.1

/-- The proof that a bundled internal-module morphism preserves module structure. -/
abbrev isModuleHom {R : RingObjCat C} {M N : ModuleObjCat R} (f : Hom M N) :
    @IsModuleHom C _ _ _ R M.X N.X M.moduleObj N.moduleObj f.1 := f.2

end Hom

/-- The identity morphism of a bundled internal module. -/
def id {R : RingObjCat C} (M : ModuleObjCat R) : Hom M M :=
  Hom.mk (𝟙 M.X) (@IsModuleHom.id C _ _ _ R M.X M.moduleObj)

/-- Composition of bundled internal-module morphisms. -/
def comp {R : RingObjCat C} {M N P : ModuleObjCat R}
    (f : Hom M N) (g : Hom N P) : Hom M P :=
  Hom.mk (f.1 ≫ g.1)
    (@IsModuleHom.comp C _ _ _ R M.X N.X P.X M.moduleObj N.moduleObj P.moduleObj
      f.1 g.1 f.2 g.2)

/-- Left identity law for bundled internal-module morphisms. -/
theorem id_comp {R : RingObjCat C} {M N : ModuleObjCat R} (f : Hom M N) :
    comp (id M) f = f := sorry

/-- Right identity law for bundled internal-module morphisms. -/
theorem comp_id {R : RingObjCat C} {M N : ModuleObjCat R} (f : Hom M N) :
    comp f (id N) = f := sorry

/-- Associativity of composition for bundled internal-module morphisms. -/
theorem assoc {R : RingObjCat C} {L M N P : ModuleObjCat R}
    (f : Hom L M) (g : Hom M N) (h : Hom N P) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Internal left modules over `R` form a category. -/
instance category (R : RingObjCat C) : Category (ModuleObjCat R) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- Bundled internal-module morphisms are determined by their underlying morphisms. -/
@[ext]
theorem hom_ext {R : RingObjCat C} {M N : ModuleObjCat R} {f g : M ⟶ N}
    (h : f.1 = g.1) : f = g := sorry

/-- The underlying morphism of an identity internal-module morphism. -/
@[simp]
theorem id_hom {R : RingObjCat C} (M : ModuleObjCat R) :
    (𝟙 M : M ⟶ M).1 = 𝟙 M.X := sorry

/-- The underlying morphism of a composite internal-module morphism. -/
@[simp]
theorem comp_hom {R : RingObjCat C} {M N P : ModuleObjCat R}
    (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).1 = f.1 ≫ g.1 := sorry

/-- The forgetful functor from internal `R`-modules to the ambient category. -/
def forget (R : RingObjCat C) : ModuleObjCat R ⥤ C where
  obj M := M.X
  map f := f.1
  map_id := id_hom
  map_comp := comp_hom

end ModuleObjCat

namespace Functor

variable {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]
variable {R : RingObjCat C}

/-- The additive-group structure on the image of an internal module. -/
noncomputable abbrev mapModuleAddGrpObj (M : ModuleObjCat R) :
    AddGrpObj (F.obj M.X) :=
  (F.mapAddGrp.obj { X := M.X, addGrp := M.moduleObj.toAddGrpObj }).addGrp

/-- Addition on the image of an internal module. -/
noncomputable abbrev mapModuleAdd (M : ModuleObjCat R) :
    F.obj M.X ⊗ F.obj M.X ⟶ F.obj M.X :=
  @AddMonObj.add D _ _ _ (mapModuleAddGrpObj F M).toAddMonObj

/-- The scalar action on the image of an internal module. -/
noncomputable def mapModuleSmul (M : ModuleObjCat R) :
    F.obj R.X ⊗ F.obj M.X ⟶ F.obj M.X :=
  LaxMonoidal.μ F R.X M.X ≫ F.map M.moduleObj.toModObj.smul

/-- The image additive-group law remains commutative. -/
theorem mapModule_isCommAddMonObj (M : ModuleObjCat R) :
    @IsCommAddMonObj D _ _ _ (F.obj M.X)
      (mapModuleAddGrpObj F M).toAddMonObj := sorry

/-- The mapped scalar action is unital. -/
theorem mapModule_one_smul (M : ModuleObjCat R) :
    @MonObj.one D _ _ _ (mapRingMonObj F R) ▷ F.obj M.X ≫ mapModuleSmul F M =
      (λ_ (F.obj M.X)).hom := sorry

/-- The mapped scalar action is associative. -/
theorem mapModule_mul_smul (M : ModuleObjCat R) :
    @MonObj.mul D _ _ _ (mapRingMonObj F R) ▷ F.obj M.X ≫ mapModuleSmul F M =
      (α_ (F.obj R.X) (F.obj R.X) (F.obj M.X)).hom ≫
        F.obj R.X ◁ mapModuleSmul F M ≫ mapModuleSmul F M := sorry

/-- Addition of mapped scalars distributes over the mapped action. -/
theorem mapModule_add_smul (M : ModuleObjCat R) :
    mapRingAdd F R ▷ F.obj M.X ≫ mapModuleSmul F M =
      lift (fst (F.obj R.X) (F.obj R.X) ▷ F.obj M.X ≫ mapModuleSmul F M)
          (snd (F.obj R.X) (F.obj R.X) ▷ F.obj M.X ≫ mapModuleSmul F M) ≫
        mapModuleAdd F M := sorry

/-- The mapped scalar action distributes over addition in the mapped module. -/
theorem mapModule_smul_add (M : ModuleObjCat R) :
    F.obj R.X ◁ mapModuleAdd F M ≫ mapModuleSmul F M =
      lift ((F.obj R.X ◁ fst (F.obj M.X) (F.obj M.X)) ≫ mapModuleSmul F M)
          ((F.obj R.X ◁ snd (F.obj M.X) (F.obj M.X)) ≫ mapModuleSmul F M) ≫
        mapModuleAdd F M := sorry

/-- The internal left-module structure carried by the image of an internal module under a
braided monoidal functor. -/
@[implicit_reducible]
noncomputable def mapModuleObj (M : ModuleObjCat R) :
    ModuleObj (mapRingObject F R) (F.obj M.X) where
  toAddGrpObj := mapModuleAddGrpObj F M
  toIsCommAddMonObj := mapModule_isCommAddMonObj F M
  toModObj :=
    { smul := mapModuleSmul F M
      one_smul := mapModule_one_smul F M
      mul_smul := mapModule_mul_smul F M }
  add_smul := mapModule_add_smul F M
  smul_add := mapModule_smul_add F M

/-- The bundled internal module obtained by applying a braided monoidal functor. -/
noncomputable def mapModuleObject (M : ModuleObjCat R) :
    ModuleObjCat (mapRingObject F R) :=
  ModuleObjCat.mk (F.obj M.X) (mapModuleObj F M)

/-- Mapping an internal-module morphism preserves addition and the scalar action. -/
theorem mapModule_isModuleHom {M N : ModuleObjCat R} (f : M ⟶ N) :
    @IsModuleHom D _ _ _ (mapRingObject F R) (F.obj M.X) (F.obj N.X)
      (mapModuleObj F M) (mapModuleObj F N) (F.map f.1) := sorry

/-- The internal-module morphism obtained by applying a braided monoidal functor. -/
noncomputable def mapModuleMap {M N : ModuleObjCat R} (f : M ⟶ N) :
    mapModuleObject F M ⟶ mapModuleObject F N :=
  ⟨F.map f.1, mapModule_isModuleHom F f⟩

/-- Mapping internal modules preserves identity morphisms. -/
theorem mapModule_map_id (M : ModuleObjCat R) :
    mapModuleMap F (𝟙 M) = 𝟙 (mapModuleObject F M) := sorry

/-- Mapping internal modules preserves composition of morphisms. -/
theorem mapModule_map_comp {M N P : ModuleObjCat R} (f : M ⟶ N) (g : N ⟶ P) :
    mapModuleMap F (f ≫ g) = mapModuleMap F f ≫ mapModuleMap F g := sorry

/-- The functor on internal left modules induced by a braided monoidal functor. -/
noncomputable def mapModule :
    ModuleObjCat R ⥤ ModuleObjCat (mapRingObject F R) where
  obj := mapModuleObject F
  map := mapModuleMap F
  map_id := mapModule_map_id F
  map_comp := mapModule_map_comp F

/-- Forgetting the internal module structure after mapping along `F` recovers `F` on
underlying objects and morphisms. -/
noncomputable def mapModuleForgetIso (R : RingObjCat C) :
    mapModule F (R := R) ⋙ ModuleObjCat.forget (mapRingObject F R) ≅
      ModuleObjCat.forget R ⋙ F :=
  Iso.refl _

/-- The canonical functor on internal modules induced by a finite-product-preserving functor.
The canonical braided structure is supplied explicitly, so callers need no local instance. -/
noncomputable def mapModuleOfFiniteProducts (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] (R : RingObjCat C) :
    ModuleObjCat R ⥤ ModuleObjCat ((mapRingOfFiniteProducts F).obj R) :=
  @mapModule C _ _ _ D _ _ _ F (Braided.ofChosenFiniteProducts F) R

/-- Forgetting internal module structure after the canonical finite-product lift recovers the
original functor on underlying objects and morphisms. -/
noncomputable def mapModuleOfFiniteProductsForgetIso (F : C ⥤ D)
    [Limits.PreservesFiniteProducts F] (R : RingObjCat C) :
    mapModuleOfFiniteProducts F R ⋙
        ModuleObjCat.forget ((mapRingOfFiniteProducts F).obj R) ≅
      ModuleObjCat.forget R ⋙ F :=
  Iso.refl _

end Functor

end CategoryTheory
