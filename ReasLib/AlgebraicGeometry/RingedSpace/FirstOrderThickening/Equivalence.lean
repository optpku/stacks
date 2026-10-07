module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.OfModule

/-!
# Equivalence between trivialized first-order thickenings and modules

The ideal-module construction identifies trivialized first-order thickenings
with the opposite of the category of modules.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- The kernel-ideal functor on trivialized first-order thickenings. -/
def idealFunctor (X : RingedSpace.{u}) : Trivialized X ⥤ (X.Modules)ᵒᵖ where
  obj T := op (RingedSpace.Hom.idealModule T.inclusion)
  map {T₁ T₂} f := (Hom.idealMap f.hom).op
  map_id := sorry
  map_comp := sorry

/-- The functor sending a module to its square-zero thickening. -/
def ofModuleFunctor (X : RingedSpace.{u}) : (X.Modules)ᵒᵖ ⥤ Trivialized X where
  obj M := ofModule M.unop
  map φ := ofModuleMap φ.unop
  map_id := sorry
  map_comp := sorry

/-- The comparison morphism from a trivialized thickening to its square-zero model. -/
def unitHom {X : RingedSpace.{u}} (T : Trivialized X) :
    T ⟶ ofModule (RingedSpace.Hom.idealModule T.inclusion) :=
  Trivialized.Hom.mk
    (Hom.mk
      (InducedCategory.homMk
        { base := T.trivialization.retraction.hom.base
          c := (@splittingIso _ _ T.inclusion T.isFirstOrder
            T.trivialization.retraction T.trivialization.id).inv.hom })
      sorry)
    sorry

/-- The inverse comparison from the square-zero model to a trivialized thickening. -/
def unitInv {X : RingedSpace.{u}} (T : Trivialized X) :
    ofModule (RingedSpace.Hom.idealModule T.inclusion) ⟶ T :=
  Trivialized.Hom.mk
    (Hom.mk
      (InducedCategory.homMk
        { base :=
            @CategoryTheory.inv _ _ _ _ T.trivialization.retraction.hom.base
              (@instIsIso_retraction_base _ _ T.inclusion T.isFirstOrder T.trivialization)
          c :=
            TopCat.Presheaf.toPushforwardOfIso
              (@asIso _ _ _ _ T.trivialization.retraction.hom.base
                (@instIsIso_retraction_base _ _ T.inclusion T.isFirstOrder T.trivialization))
              (@splittingIso _ _ T.inclusion T.isFirstOrder
                T.trivialization.retraction T.trivialization.id).hom.hom })
      sorry)
    sorry

/-- The comparison isomorphism at a trivialized thickening. -/
def unitApp {X : RingedSpace.{u}} (T : Trivialized X) :
    T ≅ ofModule (RingedSpace.Hom.idealModule T.inclusion) where
  hom := unitHom T
  inv := unitInv T
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit isomorphism of the equivalence. -/
def unitIso (X : RingedSpace.{u}) :
    𝟭 (Trivialized X) ≅ idealFunctor X ⋙ ofModuleFunctor X :=
  NatIso.ofComponents (fun T => unitApp T) sorry

/-- Morphisms of trivialized thickenings correspond to opposite ideal-module maps. -/
def homEquiv {X : RingedSpace.{u}} (T₁ T₂ : Trivialized X) :
    (T₁ ⟶ T₂) ≃
      (RingedSpace.Hom.idealModule T₂.inclusion ⟶
        RingedSpace.Hom.idealModule T₁.inclusion) where
  toFun f := Hom.idealMap f.hom
  invFun φ := unitHom T₁ ≫ ofModuleMap φ ≫ unitInv T₂
  left_inv := sorry
  right_inv := sorry

/-- The kernel module maps into the pushforward module for a square-zero extension. -/
def ofModule_kernelToPushforward {X : RingedSpace.{u}} (M : X.Modules) :
    RingedSpace.Hom.kernelIdealSheaf (inclusion M) ⟶ ((inclusion M) _*).obj M where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun x ↦
                TrivSqZeroExt.snd
                  (SheafOfModules.RingedSite.KernelIdeal.ιApp
                    (RingedSpace.Hom.commRingSheafPushforwardMap (inclusion M)) U x))
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- The pushforward module maps into the kernel module for a square-zero extension. -/
def ofModule_pushforwardToKernel {X : RingedSpace.{u}} (M : X.Modules) :
    ((inclusion M) _*).obj M ⟶ RingedSpace.Hom.kernelIdealSheaf (inclusion M) where
  val :=
    PresheafOfModules.homMk
      { app U :=
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun m ↦
                (SheafOfModules.RingedSite.KernelIdeal.sectionsIso
                    (RingedSpace.Hom.commRingSheafPushforwardMap (inclusion M)) U).inv
                  ⟨TrivSqZeroExt.inr m, TrivSqZeroExt.fst_inr _ m⟩)
              sorry
        naturality {_ _} _ := sorry }
      (fun _ _ _ ↦ sorry)

/-- `ofModule_kernelToPushforward` acts by the second square-zero projection. -/
theorem ofModule_kernelToPushforward_apply {X : RingedSpace.{u}} (M : X.Modules)
    {U : (Opens (ofModuleSpace M))ᵒᵖ}
    (x : (RingedSpace.Hom.kernelIdealSheaf (inclusion M)).val.obj U) :
    (ofModule_kernelToPushforward M).val.app U x =
      TrivSqZeroExt.snd
        (SheafOfModules.RingedSite.KernelIdeal.ιApp
          (RingedSpace.Hom.commRingSheafPushforwardMap (inclusion M)) U x) := sorry

/-- `ofModule_pushforwardToKernel` acts by the square-zero inclusion. -/
theorem ofModule_pushforwardToKernel_apply {X : RingedSpace.{u}} (M : X.Modules)
    {U : (Opens (ofModuleSpace M))ᵒᵖ}
    (m : (((inclusion M) _*).obj M).val.obj U) :
    (ofModule_pushforwardToKernel M).val.app U m =
      (SheafOfModules.RingedSite.KernelIdeal.sectionsIso
          (RingedSpace.Hom.commRingSheafPushforwardMap (inclusion M)) U).inv
        ⟨TrivSqZeroExt.inr m, TrivSqZeroExt.fst_inr _ m⟩ := sorry

/-- The kernel module of the square-zero thickening by `M` is canonically `M`. -/
def ofModule_idealIso {X : RingedSpace.{u}} (M : X.Modules) :
    RingedSpace.Hom.idealModule (inclusion M) ≅ M where
  hom :=
    ((inclusion M) ^*).map (ofModule_kernelToPushforward M) ≫
      (RingedSpace.Hom.pullbackPushforwardAdjunction (inclusion M)).counit.app M
  inv :=
    (asIso
        ((RingedSpace.Hom.pullbackPushforwardAdjunction (inclusion M)).counit.app M)).inv ≫
      ((inclusion M) ^*).map (ofModule_pushforwardToKernel M)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit isomorphism of the equivalence. -/
def counitIso (X : RingedSpace.{u}) :
    ofModuleFunctor X ⋙ idealFunctor X ≅ 𝟭 (X.Modules)ᵒᵖ :=
  NatIso.ofComponents (fun M => (ofModule_idealIso M.unop).op.symm) sorry

/-- Trivialized first-order thickenings are equivalent to opposite modules. -/
def modulesEquiv (X : RingedSpace.{u}) : Trivialized X ≌ (X.Modules)ᵒᵖ :=
  CategoryTheory.Equivalence.mk (idealFunctor X) (ofModuleFunctor X) (unitIso X) (counitIso X)

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
