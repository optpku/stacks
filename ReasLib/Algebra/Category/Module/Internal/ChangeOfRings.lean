module

public import ReasLib.Algebra.Category.Module.Internal

/-!
# Change of scalars for internal modules

This module constructs restriction of scalars for module objects over internal rings in a
braided cartesian monoidal category.  Its underlying carrier and morphisms are unchanged, while
the scalar action is pulled back along the given internal-ring morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.AddMonObj CategoryTheory.MonObj

noncomputable section

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C] [BraidedCategory C]

namespace ModuleObjCat

namespace RestrictScalars

variable {R S T : RingObjCat C}

/-- The action of `R` on an internal `S`-module obtained by precomposing with
`φ : R ⟶ S`. -/
def smul (φ : R ⟶ S) (M : ModuleObjCat S) : R.X ⊗ M.X ⟶ M.X :=
  (φ.hom ▷ M.X) ≫ M.moduleObj.toModObj.smul

/-- The restricted action is unital. -/
theorem one_smul (φ : R ⟶ S) (M : ModuleObjCat S) :
    η[R.X] ▷ M.X ≫ smul φ M = (λ_ M.X).hom := sorry

/-- The restricted action is associative. -/
theorem mul_smul (φ : R ⟶ S) (M : ModuleObjCat S) :
    μ[R.X] ▷ M.X ≫ smul φ M =
      (α_ R.X R.X M.X).hom ≫ R.X ◁ smul φ M ≫ smul φ M := sorry

/-- Addition of restricted scalars distributes over the action. -/
theorem add_smul (φ : R ⟶ S) (M : ModuleObjCat S) :
    σ[R.X] ▷ M.X ≫ smul φ M =
      lift (fst R.X R.X ▷ M.X ≫ smul φ M)
          (snd R.X R.X ▷ M.X ≫ smul φ M) ≫
        σ[M.X] := sorry

/-- The restricted action distributes over addition in the module. -/
theorem smul_add (φ : R ⟶ S) (M : ModuleObjCat S) :
    R.X ◁ σ[M.X] ≫ smul φ M =
      lift ((R.X ◁ fst M.X M.X) ≫ smul φ M)
          ((R.X ◁ snd M.X M.X) ≫ smul φ M) ≫
        σ[M.X] := sorry

/-- The internal `R`-module structure obtained by restricting an internal `S`-module along
`φ : R ⟶ S`. -/
@[implicit_reducible]
noncomputable def moduleObj (φ : R ⟶ S) (M : ModuleObjCat S) : ModuleObj R M.X where
  toAddGrpObj := M.moduleObj.toAddGrpObj
  toIsCommAddMonObj := M.moduleObj.toIsCommAddMonObj
  toModObj :=
    { smul := smul φ M
      one_smul := one_smul φ M
      mul_smul := mul_smul φ M }
  add_smul := add_smul φ M
  smul_add := smul_add φ M

/-- The bundled internal `R`-module obtained by restricting scalars along `φ : R ⟶ S`. -/
noncomputable def obj (φ : R ⟶ S) (M : ModuleObjCat S) : ModuleObjCat R where
  X := M.X
  moduleObj := moduleObj φ M

/-- Restricting scalars preserves an internal module morphism. -/
theorem isModuleHom (φ : R ⟶ S) {M N : ModuleObjCat S} (f : M ⟶ N) :
    @IsModuleHom C _ _ _ R M.X N.X (moduleObj φ M) (moduleObj φ N) f.hom := sorry

/-- The morphism between restricted internal modules induced by an `S`-module morphism. -/
noncomputable def map (φ : R ⟶ S) {M N : ModuleObjCat S} (f : M ⟶ N) :
    obj φ M ⟶ obj φ N where
  hom := f.hom
  isModuleHom := isModuleHom φ f

/-- Restriction of scalars preserves identity morphisms. -/
theorem map_id (φ : R ⟶ S) (M : ModuleObjCat S) :
    map φ (𝟙 M) = 𝟙 (obj φ M) := sorry

/-- Restriction of scalars preserves composition of morphisms. -/
theorem map_comp (φ : R ⟶ S) {M N P : ModuleObjCat S} (f : M ⟶ N) (g : N ⟶ P) :
    map φ (f ≫ g) = map φ f ≫ map φ g := sorry

end RestrictScalars

variable {R S T : RingObjCat C}

/-- Restriction of scalars for internal modules along an internal-ring morphism. -/
@[stacks 0FRE "restriction of scalars for internal modules"]
noncomputable def restrictScalars (φ : R ⟶ S) : ModuleObjCat S ⥤ ModuleObjCat R where
  obj := RestrictScalars.obj φ
  map := RestrictScalars.map φ
  map_id := RestrictScalars.map_id φ
  map_comp := RestrictScalars.map_comp φ

/-- The carrier of an internal module is unchanged by restriction of scalars. -/
@[simp]
theorem restrictScalars_obj_X (φ : R ⟶ S) (M : ModuleObjCat S) :
    ((restrictScalars φ).obj M).X = M.X := sorry

/-- The action on a restricted internal module is obtained by precomposing with the ring
morphism. -/
@[simp]
theorem restrictScalars_obj_smul (φ : R ⟶ S) (M : ModuleObjCat S) :
    ((restrictScalars φ).obj M).moduleObj.toModObj.smul =
      (φ.hom ▷ M.X) ≫ M.moduleObj.toModObj.smul := sorry

/-- The underlying morphism is unchanged by restriction of scalars. -/
@[simp]
theorem restrictScalars_map_hom (φ : R ⟶ S) {M N : ModuleObjCat S} (f : M ⟶ N) :
    ((restrictScalars φ).map f).hom = f.hom := sorry

/-- Forgetting after restriction of scalars agrees with the original forgetful functor on
carriers and morphisms. -/
noncomputable def restrictScalarsForgetIso (φ : R ⟶ S) :
    restrictScalars φ ⋙ forget R ≅ forget S :=
  Iso.refl _

/-- The forward carrier comparison after restriction of scalars is the identity. -/
@[simp]
theorem restrictScalarsForgetIso_hom_app (φ : R ⟶ S) (M : ModuleObjCat S) :
    (restrictScalarsForgetIso φ).hom.app M = 𝟙 M.X := sorry

/-- The inverse carrier comparison after restriction of scalars is the identity. -/
@[simp]
theorem restrictScalarsForgetIso_inv_app (φ : R ⟶ S) (M : ModuleObjCat S) :
    (restrictScalarsForgetIso φ).inv.app M = 𝟙 M.X := sorry

namespace RestrictScalars

namespace Congr

variable {φ ψ : R ⟶ S}

/-- The identity on carriers is linear from restriction along `φ` to restriction along an
equal ring morphism `ψ`. -/
theorem homIsModuleHom (h : φ = ψ) (M : ModuleObjCat S) :
    @IsModuleHom C _ _ _ R M.X M.X (moduleObj φ M) (moduleObj ψ M) (𝟙 M.X) := sorry

/-- The identity on carriers is linear from restriction along `ψ` to restriction along an
equal ring morphism `φ`. -/
theorem invIsModuleHom (h : φ = ψ) (M : ModuleObjCat S) :
    @IsModuleHom C _ _ _ R M.X M.X (moduleObj ψ M) (moduleObj φ M) (𝟙 M.X) := sorry

/-- The forward identity morphism comparing restriction along equal ring morphisms. -/
noncomputable def hom (h : φ = ψ) (M : ModuleObjCat S) : obj φ M ⟶ obj ψ M where
  hom := 𝟙 M.X
  isModuleHom := homIsModuleHom h M

/-- The inverse identity morphism comparing restriction along equal ring morphisms. -/
noncomputable def inv (h : φ = ψ) (M : ModuleObjCat S) : obj ψ M ⟶ obj φ M where
  hom := 𝟙 M.X
  isModuleHom := invIsModuleHom h M

/-- The forward and inverse comparison maps compose to the identity. -/
theorem hom_inv_id (h : φ = ψ) (M : ModuleObjCat S) :
    hom h M ≫ inv h M = 𝟙 (obj φ M) := sorry

/-- The inverse and forward comparison maps compose to the identity. -/
theorem inv_hom_id (h : φ = ψ) (M : ModuleObjCat S) :
    inv h M ≫ hom h M = 𝟙 (obj ψ M) := sorry

/-- The componentwise isomorphism comparing restriction along equal ring morphisms. -/
noncomputable def app (h : φ = ψ) (M : ModuleObjCat S) : obj φ M ≅ obj ψ M where
  hom := hom h M
  inv := inv h M
  hom_inv_id := hom_inv_id h M
  inv_hom_id := inv_hom_id h M

/-- The underlying forward map of the equality comparison is the identity. -/
@[simp]
theorem app_hom_hom (h : φ = ψ) (M : ModuleObjCat S) :
    (app h M).hom.hom = 𝟙 M.X := sorry

/-- The underlying inverse map of the equality comparison is the identity. -/
@[simp]
theorem app_inv_hom (h : φ = ψ) (M : ModuleObjCat S) :
    (app h M).inv.hom = 𝟙 M.X := sorry

/-- The forward equality-comparison components are natural. -/
theorem hom_naturality (h : φ = ψ) {M N : ModuleObjCat S} (f : M ⟶ N) :
    (restrictScalars φ).map f ≫ (app h N).hom =
      (app h M).hom ≫ (restrictScalars ψ).map f := sorry

/-- The inverse equality-comparison components are natural. -/
theorem inv_naturality (h : φ = ψ) {M N : ModuleObjCat S} (f : M ⟶ N) :
    (restrictScalars ψ).map f ≫ (app h N).inv =
      (app h M).inv ≫ (restrictScalars φ).map f := sorry

/-- The forward natural transformation comparing restriction along equal ring morphisms. -/
noncomputable def natHom (h : φ = ψ) : restrictScalars φ ⟶ restrictScalars ψ where
  app M := (app h M).hom
  naturality := fun {M N} f ↦
    hom_naturality (φ := φ) (ψ := ψ) h (M := M) (N := N) f

/-- The inverse natural transformation comparing restriction along equal ring morphisms. -/
noncomputable def natInv (h : φ = ψ) : restrictScalars ψ ⟶ restrictScalars φ where
  app M := (app h M).inv
  naturality := fun {M N} f ↦
    inv_naturality (φ := φ) (ψ := ψ) h (M := M) (N := N) f

/-- The forward and inverse equality-comparison transformations compose to the identity. -/
theorem natHom_inv (h : φ = ψ) :
    natHom h ≫ natInv h = 𝟙 (restrictScalars φ) := sorry

/-- The inverse and forward equality-comparison transformations compose to the identity. -/
theorem natInv_hom (h : φ = ψ) :
    natInv h ≫ natHom h = 𝟙 (restrictScalars ψ) := sorry

end Congr

end RestrictScalars

/-- Equal morphisms of internal rings induce naturally isomorphic restriction-of-scalars
functors. -/
noncomputable def restrictScalarsCongr {φ ψ : R ⟶ S} (h : φ = ψ) :
    restrictScalars φ ≅ restrictScalars ψ where
  hom := RestrictScalars.Congr.natHom h
  inv := RestrictScalars.Congr.natInv h
  hom_inv_id := RestrictScalars.Congr.natHom_inv h
  inv_hom_id := RestrictScalars.Congr.natInv_hom h

namespace RestrictScalars

namespace Identity

/-- The identity on carriers is linear from restriction along the identity ring morphism to
the original internal module. -/
theorem homIsModuleHom (R : RingObjCat C) (M : ModuleObjCat R) :
    @IsModuleHom C _ _ _ R M.X M.X (moduleObj (𝟙 R) M) M.moduleObj (𝟙 M.X) := sorry

/-- The identity on carriers is linear from an internal module to its restriction along the
identity ring morphism. -/
theorem invIsModuleHom (R : RingObjCat C) (M : ModuleObjCat R) :
    @IsModuleHom C _ _ _ R M.X M.X M.moduleObj (moduleObj (𝟙 R) M) (𝟙 M.X) := sorry

/-- The forward identity comparison morphism for restriction of scalars. -/
noncomputable def hom (R : RingObjCat C) (M : ModuleObjCat R) : obj (𝟙 R) M ⟶ M where
  hom := 𝟙 M.X
  isModuleHom := homIsModuleHom R M

/-- The inverse identity comparison morphism for restriction of scalars. -/
noncomputable def inv (R : RingObjCat C) (M : ModuleObjCat R) : M ⟶ obj (𝟙 R) M where
  hom := 𝟙 M.X
  isModuleHom := invIsModuleHom R M

/-- The two identity comparison morphisms compose to the identity on the restricted module. -/
theorem hom_inv_id (R : RingObjCat C) (M : ModuleObjCat R) :
    hom R M ≫ inv R M = 𝟙 (obj (𝟙 R) M) := sorry

/-- The two identity comparison morphisms compose to the identity on the original module. -/
theorem inv_hom_id (R : RingObjCat C) (M : ModuleObjCat R) :
    inv R M ≫ hom R M = 𝟙 M := sorry

/-- The componentwise comparison between restriction along the identity and the identity
functor. -/
noncomputable def app (R : RingObjCat C) (M : ModuleObjCat R) : obj (𝟙 R) M ≅ M where
  hom := hom R M
  inv := inv R M
  hom_inv_id := hom_inv_id R M
  inv_hom_id := inv_hom_id R M

/-- The underlying forward identity-comparison map is the identity. -/
@[simp]
theorem app_hom_hom (R : RingObjCat C) (M : ModuleObjCat R) :
    (app R M).hom.hom = 𝟙 M.X := sorry

/-- The underlying inverse identity-comparison map is the identity. -/
@[simp]
theorem app_inv_hom (R : RingObjCat C) (M : ModuleObjCat R) :
    (app R M).inv.hom = 𝟙 M.X := sorry

/-- The forward identity-comparison components are natural. -/
theorem hom_naturality (R : RingObjCat C) {M N : ModuleObjCat R} (f : M ⟶ N) :
    (restrictScalars (𝟙 R)).map f ≫ (app R N).hom =
      (app R M).hom ≫ (𝟭 (ModuleObjCat R)).map f := sorry

/-- The inverse identity-comparison components are natural. -/
theorem inv_naturality (R : RingObjCat C) {M N : ModuleObjCat R} (f : M ⟶ N) :
    (𝟭 (ModuleObjCat R)).map f ≫ (app R N).inv =
      (app R M).inv ≫ (restrictScalars (𝟙 R)).map f := sorry

/-- The forward natural transformation from restriction along the identity to the identity
functor. -/
noncomputable def natHom (R : RingObjCat C) : restrictScalars (𝟙 R) ⟶ 𝟭 (ModuleObjCat R) where
  app M := (app R M).hom
  naturality := fun {M N} f ↦ hom_naturality R (M := M) (N := N) f

/-- The inverse natural transformation from the identity functor to restriction along the
identity. -/
noncomputable def natInv (R : RingObjCat C) : 𝟭 (ModuleObjCat R) ⟶ restrictScalars (𝟙 R) where
  app M := (app R M).inv
  naturality := fun {M N} f ↦ inv_naturality R (M := M) (N := N) f

/-- The forward and inverse identity-comparison transformations compose to the identity. -/
theorem natHom_inv (R : RingObjCat C) :
    natHom R ≫ natInv R = 𝟙 (restrictScalars (𝟙 R)) := sorry

/-- The inverse and forward identity-comparison transformations compose to the identity. -/
theorem natInv_hom (R : RingObjCat C) :
    natInv R ≫ natHom R = 𝟙 (𝟭 (ModuleObjCat R)) := sorry

end Identity

end RestrictScalars

/-- Restriction along the identity internal-ring morphism is naturally isomorphic to the
identity functor. -/
noncomputable def restrictScalarsId (R : RingObjCat C) :
    restrictScalars (𝟙 R) ≅ 𝟭 (ModuleObjCat R) where
  hom := RestrictScalars.Identity.natHom R
  inv := RestrictScalars.Identity.natInv R
  hom_inv_id := RestrictScalars.Identity.natHom_inv R
  inv_hom_id := RestrictScalars.Identity.natInv_hom R

namespace RestrictScalars

namespace Comp

variable (φ : R ⟶ S) (ψ : S ⟶ T)

/-- The identity on carriers is linear from restriction along a composite to successive
restriction. -/
theorem homIsModuleHom (M : ModuleObjCat T) :
    @IsModuleHom C _ _ _ R M.X M.X (moduleObj (φ ≫ ψ) M)
      (moduleObj φ (obj ψ M)) (𝟙 M.X) := sorry

/-- The identity on carriers is linear from successive restriction to restriction along the
composite. -/
theorem invIsModuleHom (M : ModuleObjCat T) :
    @IsModuleHom C _ _ _ R M.X M.X (moduleObj φ (obj ψ M))
      (moduleObj (φ ≫ ψ) M) (𝟙 M.X) := sorry

/-- The forward comparison morphism from restriction along a composite to successive
restriction. -/
noncomputable def hom (M : ModuleObjCat T) : obj (φ ≫ ψ) M ⟶ obj φ (obj ψ M) where
  hom := 𝟙 M.X
  isModuleHom := homIsModuleHom φ ψ M

/-- The inverse comparison morphism from successive restriction to restriction along a
composite. -/
noncomputable def inv (M : ModuleObjCat T) : obj φ (obj ψ M) ⟶ obj (φ ≫ ψ) M where
  hom := 𝟙 M.X
  isModuleHom := invIsModuleHom φ ψ M

/-- The composition comparison maps compose to the identity on restriction along the
composite. -/
theorem hom_inv_id (M : ModuleObjCat T) :
    hom φ ψ M ≫ inv φ ψ M = 𝟙 (obj (φ ≫ ψ) M) := sorry

/-- The composition comparison maps compose to the identity on successive restriction. -/
theorem inv_hom_id (M : ModuleObjCat T) :
    inv φ ψ M ≫ hom φ ψ M = 𝟙 (obj φ (obj ψ M)) := sorry

/-- The componentwise comparison between restriction along a composite and successive
restriction. -/
noncomputable def app (M : ModuleObjCat T) : obj (φ ≫ ψ) M ≅ obj φ (obj ψ M) where
  hom := hom φ ψ M
  inv := inv φ ψ M
  hom_inv_id := hom_inv_id φ ψ M
  inv_hom_id := inv_hom_id φ ψ M

/-- The underlying forward composition-comparison map is the identity. -/
@[simp]
theorem app_hom_hom (M : ModuleObjCat T) : (app φ ψ M).hom.hom = 𝟙 M.X := sorry

/-- The underlying inverse composition-comparison map is the identity. -/
@[simp]
theorem app_inv_hom (M : ModuleObjCat T) : (app φ ψ M).inv.hom = 𝟙 M.X := sorry

/-- The forward composition-comparison components are natural. -/
theorem hom_naturality {M N : ModuleObjCat T} (f : M ⟶ N) :
    (restrictScalars (φ ≫ ψ)).map f ≫ (app φ ψ N).hom =
      (app φ ψ M).hom ≫ (restrictScalars ψ ⋙ restrictScalars φ).map f := sorry

/-- The inverse composition-comparison components are natural. -/
theorem inv_naturality {M N : ModuleObjCat T} (f : M ⟶ N) :
    (restrictScalars ψ ⋙ restrictScalars φ).map f ≫ (app φ ψ N).inv =
      (app φ ψ M).inv ≫ (restrictScalars (φ ≫ ψ)).map f := sorry

/-- The forward natural transformation from restriction along a composite to successive
restriction. -/
noncomputable def natHom :
    restrictScalars (φ ≫ ψ) ⟶ restrictScalars ψ ⋙ restrictScalars φ where
  app M := (app φ ψ M).hom
  naturality := fun {M N} f ↦ hom_naturality φ ψ (M := M) (N := N) f

/-- The inverse natural transformation from successive restriction to restriction along a
composite. -/
noncomputable def natInv :
    restrictScalars ψ ⋙ restrictScalars φ ⟶ restrictScalars (φ ≫ ψ) where
  app M := (app φ ψ M).inv
  naturality := fun {M N} f ↦ inv_naturality φ ψ (M := M) (N := N) f

/-- The forward and inverse composition-comparison transformations compose to the identity. -/
theorem natHom_inv : natHom φ ψ ≫ natInv φ ψ = 𝟙 (restrictScalars (φ ≫ ψ)) := sorry

/-- The inverse and forward composition-comparison transformations compose to the identity. -/
theorem natInv_hom :
    natInv φ ψ ≫ natHom φ ψ = 𝟙 (restrictScalars ψ ⋙ restrictScalars φ) := sorry

end Comp

end RestrictScalars

/-- Restriction along a composite internal-ring morphism is naturally isomorphic to successive
restriction of scalars. -/
noncomputable def restrictScalarsComp (φ : R ⟶ S) (ψ : S ⟶ T) :
    restrictScalars (φ ≫ ψ) ≅ restrictScalars ψ ⋙ restrictScalars φ where
  hom := RestrictScalars.Comp.natHom φ ψ
  inv := RestrictScalars.Comp.natInv φ ψ
  hom_inv_id := RestrictScalars.Comp.natHom_inv φ ψ
  inv_hom_id := RestrictScalars.Comp.natInv_hom φ ψ

namespace RestrictScalars

namespace Equivalence

/-- The unit comparison for restriction of scalars along an internal-ring isomorphism. -/
noncomputable def unitIso (e : R ≅ S) :
    𝟭 (ModuleObjCat S) ≅ restrictScalars e.hom ⋙ restrictScalars e.inv :=
    (restrictScalarsId S).symm ≪≫
      restrictScalarsCongr e.inv_hom_id.symm ≪≫
        restrictScalarsComp e.inv e.hom

/-- The counit comparison for restriction of scalars along an internal-ring isomorphism. -/
noncomputable def counitIso (e : R ≅ S) :
    restrictScalars e.inv ⋙ restrictScalars e.hom ≅ 𝟭 (ModuleObjCat R) :=
    (restrictScalarsComp e.hom e.inv).symm ≪≫
      restrictScalarsCongr e.hom_inv_id ≪≫
        restrictScalarsId R

/-- The unit and counit comparisons for restriction along an internal-ring isomorphism satisfy
the triangle identity. -/
theorem triangle (e : R ≅ S) :
    ∀ M : ModuleObjCat S,
      (restrictScalars e.hom).map ((unitIso e).hom.app M) ≫
          (counitIso e).hom.app ((restrictScalars e.hom).obj M) =
        𝟙 ((restrictScalars e.hom).obj M) := sorry

end Equivalence

end RestrictScalars

/-- An isomorphism of internal rings induces an equivalence between their categories of
internal modules by restriction of scalars. -/
@[stacks 0FRE "transport of internal modules along an internal-ring isomorphism"]
noncomputable def restrictScalarsEquivalence (e : R ≅ S) :
    ModuleObjCat S ≌ ModuleObjCat R where
  functor := restrictScalars e.hom
  inverse := restrictScalars e.inv
  unitIso := RestrictScalars.Equivalence.unitIso e
  counitIso := RestrictScalars.Equivalence.counitIso e
  functor_unitIso_comp := RestrictScalars.Equivalence.triangle e

/-- Restriction of scalars along an internal-ring isomorphism is an equivalence of
categories. -/
noncomputable instance restrictScalarsIsEquivalence (e : R ≅ S) :
    (restrictScalars e.hom).IsEquivalence :=
  (restrictScalarsEquivalence e).isEquivalence_functor

end ModuleObjCat

end CategoryTheory
