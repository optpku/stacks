module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.CategoryTheory.Sites.LocalIsoDescent

/-!
# Descent of locally specified scalar actions

A locally terminal presheaf indexes local scalar actions on a given additive sheaf. The global
scalar function is the sheaf amalgamation of those local actions. The additive carrier and
restriction maps remain those of the given sheaf.
-/

@[expose] public section

open CategoryTheory Opposite
noncomputable section
universe u v w

namespace CategoryTheory.Sheaf.LocalActionDescent

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Sheaf J RingCat.{w}) (F : Sheaf J AddCommGrpCat.{w})
variable (P : Cᵒᵖ ⥤ Type w)

/-- Ring sections together with additive sections, before choosing a local chart. -/
def pairs : Cᵒᵖ ⥤ Type w where
  obj T := R.obj.obj T × F.obj.obj T
  map f := TypeCat.ofHom fun x ↦ (R.obj.map f x.1, F.obj.map f x.2)
  map_id T := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- A pair together with an actual local index. -/
def localPairs : Cᵒᵖ ⥤ Type w where
  obj T := P.obj T × (pairs J R F).obj T
  map f := TypeCat.ofHom fun x ↦ (P.map f x.1, (pairs J R F).map f x.2)
  map_id := sorry
  map_comp := sorry

/-- Forget the local index, preserving the actual ring and additive sections. -/
def forgetIndex : localPairs J R F P ⟶ pairs J R F where
  app T := TypeCat.ofHom fun x ↦ x.2
  naturality _ _ _ := rfl

/-- A locally inhabited index supplies local preimages of every pair of sections. -/
instance forgetIndex_locallySurjective
    [Presheaf.IsLocallySurjective J (Limits.terminal.from P)] :
    Presheaf.IsLocallySurjective J (forgetIndex J R F P) := sorry

/-- Local uniqueness of the index makes forgetting it locally injective. -/
instance forgetIndex_locallyInjective
    [Presheaf.IsLocallyInjective J (Limits.terminal.from P)] :
    Presheaf.IsLocallyInjective J (forgetIndex J R F P) := sorry

/-- Concrete local scalar functions and their correct laws. The input is local operation data,
not a global module or an assertion that one exists. -/
structure LocalAction where
  smul : ∀ T : Cᵒᵖ, P.obj T → R.obj.obj T → F.obj.obj T → F.obj.obj T
  naturality : ∀ {T V : Cᵒᵖ} (f : T ⟶ V) (i : P.obj T)
    (r : R.obj.obj T) (x : F.obj.obj T),
    F.obj.map f (smul T i r x) = smul V (P.map f i) (R.obj.map f r) (F.obj.map f x)
  one_smul : ∀ T i x, smul T i 1 x = x
  mul_smul : ∀ T i r s x, smul T i (r * s) x = smul T i r (smul T i s x)
  smul_add : ∀ T i r x y, smul T i r (x + y) = smul T i r x + smul T i r y
  smul_zero : ∀ T i r, smul T i r 0 = 0
  add_smul : ∀ T i r s x, smul T i (r + s) x = smul T i r x + smul T i s x
  zero_smul : ∀ T i x, smul T i 0 x = 0

variable (A : LocalAction J R F P)

/-- The local operation, regarded as a morphism into the underlying Type sheaf. -/
def localScalar : localPairs J R F P ⟶ F.obj ⋙ forget AddCommGrpCat.{w} where
  app T := TypeCat.ofHom fun x ↦ A.smul T x.1 x.2.1 x.2.2
  naturality T V f := by
    ext x
    exact (A.naturality f x.1 x.2.1 x.2.2).symm

variable [Presheaf.IsLocallySurjective J (forgetIndex J R F P)]
variable [Presheaf.IsLocallyInjective J (forgetIndex J R F P)]

/-- The global scalar is the explicit native sheaf amalgamation of the local scalar values. -/
def scalar {T : Cᵒᵖ} (r : R.obj.obj T) (x : F.obj.obj T) : F.obj.obj T :=
  Presheaf.LocalIsoDescent.app J (forgetIndex J R F P) (localScalar J R F P A)
    (((sheafCompose J (forget AddCommGrpCat.{w})).obj F).property) (r, x)

/-- Restricting the glued scalar to any actual local preimage gives its prescribed local value. -/
theorem scalar_restrict {T : Cᵒᵖ} (r : R.obj.obj T) (x : F.obj.obj T)
    {V : C} (f : V ⟶ T.unop)
    (hf : Presheaf.imageSieve (A := Type w) (FA := TypeCat.Fun)
      (U := T.unop) (forgetIndex J R F P) ((r, x) : (pairs J R F).obj T) f) :
    F.obj.map f.op (scalar J R F P A r x) =
      (localScalar J R F P A).app (op V)
        (Presheaf.localPreimage (A := Type w) (FA := TypeCat.Fun) (U := T)
          (forgetIndex J R F P) ((r, x) : (pairs J R F).obj T) f hf) :=
  Presheaf.LocalIsoDescent.app_restrict J (forgetIndex J R F P)
    (localScalar J R F P A) (((sheafCompose J (forget AddCommGrpCat.{w})).obj F).property) (r, x) f hf

/-- Scalar multiplication commutes with the original restriction maps. -/
theorem scalar_naturality {T V : Cᵒᵖ} (f : T ⟶ V)
    (r : R.obj.obj T) (x : F.obj.obj T) :
    F.obj.map f (scalar J R F P A r x) =
      scalar J R F P A (R.obj.map f r) (F.obj.map f x) :=
  Presheaf.LocalIsoDescent.app_natural J (forgetIndex J R F P)
    (localScalar J R F P A) (((sheafCompose J (forget AddCommGrpCat.{w})).obj F).property) f (r, x)

theorem scalar_one (T : Cᵒᵖ) (x : F.obj.obj T) : scalar J R F P A 1 x = x := sorry
theorem scalar_mul (T : Cᵒᵖ) (r s : R.obj.obj T) (x : F.obj.obj T) :
    scalar J R F P A (r * s) x = scalar J R F P A r (scalar J R F P A s x) := sorry
theorem scalar_add (T : Cᵒᵖ) (r : R.obj.obj T) (x y : F.obj.obj T) :
    scalar J R F P A r (x + y) = scalar J R F P A r x + scalar J R F P A r y := sorry
theorem scalar_zero (T : Cᵒᵖ) (r : R.obj.obj T) : scalar J R F P A r 0 = 0 := sorry
theorem add_scalar (T : Cᵒᵖ) (r s : R.obj.obj T) (x : F.obj.obj T) :
    scalar J R F P A (r + s) x = scalar J R F P A r x + scalar J R F P A s x := sorry
theorem zero_scalar (T : Cᵒᵖ) (x : F.obj.obj T) : scalar J R F P A 0 x = 0 := sorry

/-- The descended module has the existing additive carrier and the specified scalar function. -/
@[implicit_reducible]
def sectionModule (T : Cᵒᵖ) : Module (R.obj.obj T) (F.obj.obj T) where
  smul := scalar J R F P A
  one_smul := scalar_one J R F P A T
  mul_smul := scalar_mul J R F P A T
  smul_add := scalar_add J R F P A T
  smul_zero := scalar_zero J R F P A T
  add_smul := add_scalar J R F P A T
  zero_smul := zero_scalar J R F P A T

/-- Bundle the original additive sections with the descended module structure. -/
def sectionObj (T : Cᵒᵖ) : ModuleCat.{w} (R.obj.obj T) :=
  letI := sectionModule J R F P A T
  ModuleCat.of (R.obj.obj T) (F.obj.obj T)

/-- Module restriction is exactly restriction in the given additive sheaf. -/
def restriction {T V : Cᵒᵖ} (f : T ⟶ V) :
    sectionObj J R F P A T ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj (sectionObj J R F P A V) :=
  letI := sectionModule J R F P A T
  letI := sectionModule J R F P A V
  ModuleCat.ofHom
    (X := sectionObj J R F P A T)
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj (sectionObj J R F P A V))
    { toFun := F.obj.map f
      map_add' := (F.obj.map f).hom.map_add
      map_smul' := scalar_naturality J R F P A f }

/-- The global presheaf uses the given additive carrier and restriction maps. -/
def presheaf : PresheafOfModules.{w} R.obj where
  obj := sectionObj J R F P A
  map := restriction J R F P A
  map_id := sorry
  map_comp := sorry

/-- The descended module presheaf is a sheaf because its underlying additive sheaf is `F`. -/
theorem presheaf_isSheaf : Presheaf.IsSheaf J (presheaf J R F P A).presheaf := sorry

/-- The actual global module obtained from local scalar actions by sheaf amalgamation. -/
def module : SheafOfModules.{w} R :=
  ⟨presheaf J R F P A, presheaf_isSheaf J R F P A⟩

/-- Forgetting the descended scalars recovers the given additive sheaf by identity functions
in both directions. -/
def underlyingIso : (SheafOfModules.toSheaf R).obj (module J R F P A) ≅ F where
  hom := ⟨{ app := fun T ↦ AddCommGrpCat.ofHom (AddMonoidHom.id (F.obj.obj T))
            naturality := sorry }⟩
  inv := ⟨{ app := fun T ↦ AddCommGrpCat.ofHom (AddMonoidHom.id (F.obj.obj T))
            naturality := sorry }⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forgetful comparison has the literal identity forward function. -/
@[simp]
theorem underlyingIso_hom_apply (T : Cᵒᵖ) (x : (module J R F P A).val.obj T) :
    (underlyingIso J R F P A).hom.hom.app T x = x := rfl

/-- The reverse forgetful comparison has the literal identity function. -/
@[simp]
theorem underlyingIso_inv_apply (T : Cᵒᵖ) (x : F.obj.obj T) :
    (underlyingIso J R F P A).inv.hom.app T x = x := rfl

end CategoryTheory.Sheaf.LocalActionDescent
