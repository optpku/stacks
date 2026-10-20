module

public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

@[expose] public section

open CategoryTheory

universe u₀ v₀ u₁ v₁ w

namespace CategoryTheory.Sheaf.InternalModule

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget RingCat.{w})]

/-- The component function with its module carriers retained for instance
inference. Forgetting to a type-valued sheaf erases these bundled instances. -/
noncomputable def underlyingApp (R : Sheaf J RingCat.{w})
    {M N : SheafOfModules.{w} R}
    (α : (ToInternal.underlying R).obj M ⟶ (ToInternal.underlying R).obj N)
    (U : Cᵒᵖ) : M.val.obj U → N.val.obj U := α.hom.app U

/-- Lift a genuinely additive and linear map of underlying sheaves to a
module map. The function is supplied explicitly; no morphism is chosen from
an existence statement. -/
noncomputable def homOfUnderlying (R : Sheaf J RingCat.{w})
    {M N : SheafOfModules.{w} R}
    (α : (ToInternal.underlying R).obj M ⟶ (ToInternal.underlying R).obj N)
    (ha : ∀ U (x y : M.val.obj U),
      underlyingApp R α U (x + y) =
        underlyingApp R α U x + underlyingApp R α U y)
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U),
      underlyingApp R α U (r • x) = r • underlyingApp R α U x) :
    M ⟶ N where
  val :=
    { app := fun U ↦
        @ModuleCat.ofHom (R.obj.obj U) _ (M.val.obj U) (N.val.obj U)
          (M.val.obj U).isAddCommGroup (M.val.obj U).isModule
          (N.val.obj U).isAddCommGroup (N.val.obj U).isModule
          { toFun := α.hom.app U
            map_add' := ha U
            map_smul' := hs U }
      naturality := sorry }

/-- Lift an isomorphism of underlying sheaf-valued functors whose forward components
preserve addition and scalar multiplication. The given inverse functions are retained. -/
noncomputable def functorIsoOfUnderlying {A : Type u₁} [Category.{v₁} A]
    (R : Sheaf J RingCat.{w}) {F G : A ⥤ SheafOfModules.{w} R}
    (e : F ⋙ ToInternal.underlying R ≅ G ⋙ ToInternal.underlying R)
    (ha : ∀ M U (x y : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (x + y) =
        underlyingApp R (e.hom.app M) U x + underlyingApp R (e.hom.app M) U y)
    (hs : ∀ M U (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (r • x) =
        r • underlyingApp R (e.hom.app M) U x) : F ≅ G :=
  NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        LinearEquiv.toModuleIso
          { ((((sheafToPresheaf J (Type w)).mapIso (e.app M)).app U).toEquiv) with
            map_add' := ha M U
            map_smul' := hs M U }) (by sorry))) (by sorry)

/-- The lifted forward map is the supplied underlying component function. -/
@[simp]
theorem functorIsoOfUnderlying_hom_app {A : Type u₁} [Category.{v₁} A]
    (R : Sheaf J RingCat.{w}) {F G : A ⥤ SheafOfModules.{w} R}
    (e : F ⋙ ToInternal.underlying R ≅ G ⋙ ToInternal.underlying R)
    (ha : ∀ M U (x y : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (x + y) =
        underlyingApp R (e.hom.app M) U x + underlyingApp R (e.hom.app M) U y)
    (hs : ∀ M U (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (r • x) =
        r • underlyingApp R (e.hom.app M) U x)
    (M : A) (U : Cᵒᵖ) (x : (F.obj M).val.obj U) :
    (((functorIsoOfUnderlying R e ha hs).hom.app M).val.app U).hom x =
      underlyingApp R (e.hom.app M) U x := rfl

/-- The lifted inverse map is the supplied inverse component function. -/
@[simp]
theorem functorIsoOfUnderlying_inv_app {A : Type u₁} [Category.{v₁} A]
    (R : Sheaf J RingCat.{w}) {F G : A ⥤ SheafOfModules.{w} R}
    (e : F ⋙ ToInternal.underlying R ≅ G ⋙ ToInternal.underlying R)
    (ha : ∀ M U (x y : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (x + y) =
        underlyingApp R (e.hom.app M) U x + underlyingApp R (e.hom.app M) U y)
    (hs : ∀ M U (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      underlyingApp R (e.hom.app M) U (r • x) =
        r • underlyingApp R (e.hom.app M) U x)
    (M : A) (U : Cᵒᵖ) (x : (G.obj M).val.obj U) :
    (((functorIsoOfUnderlying R e ha hs).inv.app M).val.app U).hom x =
      underlyingApp R (e.inv.app M) U x := rfl

end CategoryTheory.Sheaf.InternalModule

namespace CategoryTheory.MorphismOfTopoiIn

variable {C₀ : Type u₀} [Category.{v₀} C₀] {J₀ : GrothendieckTopology C₀}
variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
variable [J₀.HasSheafCompose (forget RingCat.{w})]
variable [J₁.HasSheafCompose (forget RingCat.{w})]
variable (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
variable (R : Sheaf J₀ RingCat.{w})

/-- Direct image over the original coefficient ring: after module direct
image, restrict scalars along the actual ring-adjunction unit. -/
noncomputable def moduleRightOver :
    SheafOfModules.{w} (f.ringInverseImage.obj R) ⥤ SheafOfModules.{w} R :=
  f.moduleDirectImage (f.ringInverseImage.obj R) ⋙
    SheafOfModules.restrictScalars (f.ringAdjunction.unit.app R)

/-- Restricting scalars does not change the underlying sheaf, so the direct
image comparison remains the canonical one. -/
noncomputable def moduleRightOverForgetIso :
    f.moduleRightOver R ⋙ Sheaf.InternalModule.ToInternal.underlying R ≅
      Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R) ⋙ f.pushforward :=
  f.moduleDirectImageForgetIso (f.ringInverseImage.obj R)

/-- The forward mate on underlying sheaves, transported along the canonical
forgetful comparisons on both sides. -/
noncomputable def moduleMateUnderlying
    (A : SheafOfModules.{w} R)
    (B : SheafOfModules.{w} (f.ringInverseImage.obj R))
    (h : (f.moduleInverseImage R).obj A ⟶ B) :
    (Sheaf.InternalModule.ToInternal.underlying R).obj A ⟶
      (Sheaf.InternalModule.ToInternal.underlying R).obj ((f.moduleRightOver R).obj B) :=
  (f.adjunction.homEquiv _ _)
      ((f.moduleInverseImageForgetIso R).inv.app A ≫
        (Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R)).map h) ≫
    (f.moduleRightOverForgetIso R).inv.app B

/-- The backward mate on underlying sheaves uses the inverse of the same
topos adjunction; no arbitrary comparison map is introduced. -/
noncomputable def moduleUnmateUnderlying
    (A : SheafOfModules.{w} R)
    (B : SheafOfModules.{w} (f.ringInverseImage.obj R))
    (h : A ⟶ (f.moduleRightOver R).obj B) :
    (Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R)).obj
        ((f.moduleInverseImage R).obj A) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (f.ringInverseImage.obj R)).obj B :=
  (f.moduleInverseImageForgetIso R).hom.app A ≫
    (f.adjunction.homEquiv _ _).symm
      ((Sheaf.InternalModule.ToInternal.underlying R).map h ≫
        (f.moduleRightOverForgetIso R).hom.app B)

/-- Lift the forward mate to modules over the original ring. Additivity and
linearity are laws of the specified mate, not extra choices of data. -/
noncomputable def moduleMate
    (A : SheafOfModules.{w} R)
    (B : SheafOfModules.{w} (f.ringInverseImage.obj R))
    (h : (f.moduleInverseImage R).obj A ⟶ B) :
    A ⟶ (f.moduleRightOver R).obj B :=
  Sheaf.InternalModule.homOfUnderlying R (f.moduleMateUnderlying R A B h) sorry sorry

/-- Lift the backward mate over the inverse-image ring. -/
noncomputable def moduleUnmate
    (A : SheafOfModules.{w} R)
    (B : SheafOfModules.{w} (f.ringInverseImage.obj R))
    (h : A ⟶ (f.moduleRightOver R).obj B) :
    (f.moduleInverseImage R).obj A ⟶ B :=
  Sheaf.InternalModule.homOfUnderlying (f.ringInverseImage.obj R)
    (f.moduleUnmateUnderlying R A B h) sorry sorry

/-- The coefficient-varying module Hom equivalence has explicit forward
and backward maps induced by the underlying topos adjunction. -/
noncomputable def moduleHomEquiv
    (A : SheafOfModules.{w} R)
    (B : SheafOfModules.{w} (f.ringInverseImage.obj R)) :
    ((f.moduleInverseImage R).obj A ⟶ B) ≃ (A ⟶ (f.moduleRightOver R).obj B) where
  toFun := f.moduleMate R A B
  invFun := f.moduleUnmate R A B
  left_inv := sorry
  right_inv := sorry

/-- Inverse image of modules is left adjoint to direct image followed by
restriction along the ring unit. The Hom equivalence is fixed canonically. -/
noncomputable def moduleAdjunction : f.moduleInverseImage R ⊣ f.moduleRightOver R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := f.moduleHomEquiv R
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end CategoryTheory.MorphismOfTopoiIn
