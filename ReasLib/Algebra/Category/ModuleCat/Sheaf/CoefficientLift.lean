/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.RingTheory.FreeRing

/-! # Coefficient lifting with unchanged module carriers -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

universe c v u

namespace SheafOfModules.CoefficientLift

/-- A ring element is the image of the generator of the free ring on one generator. -/
private def ringForgetIso :
    coyoneda.obj (op (RingCat.of (FreeRing PUnit.{u + 1}))) ≅
      CategoryTheory.forget RingCat.{u} :=
  NatIso.ofComponents (fun R ↦ Equiv.toIso
    { toFun := fun f ↦ f.hom (FreeRing.of PUnit.unit)
      invFun := fun r ↦ RingCat.ofHom (FreeRing.lift (fun _ ↦ r))
      left_inv := fun f ↦ by
        apply RingCat.hom_ext
        apply FreeRing.hom_ext
        intro x
        cases x
        exact FreeRing.lift_of _ _
      right_inv := fun r ↦ FreeRing.lift_of _ _ })
    (fun f ↦ by ext g; rfl)

/-- The underlying set functor preserves limits of every specified size. -/
private instance ringForgetPreservesLimits :
    PreservesLimitsOfSize.{v, c} (CategoryTheory.forget RingCat.{u}) :=
  preservesLimits_of_natIso ringForgetIso

/-- A limiting cone of underlying sets gives the original ring cone its limit law. -/
private theorem ringForgetReflectsLimit {D : Type c} [Category.{v} D]
    (F : D ⥤ RingCat.{u}) : ReflectsLimit F (CategoryTheory.forget RingCat.{u}) where
  reflects {s} hs := by
    -- Local instance justification (proof-local temporary data): the supplied limiting cone makes its section type small, enabling the explicit ring limit for this diagram.
    letI : HasLimit (F ⋙ CategoryTheory.forget RingCat.{u}) := ⟨_, hs⟩
    -- Local instance justification (proof-local temporary data): this smallness comes from the supplied cone and is needed only to construct the same diagram's ring limit.
    letI : Small.{u} (F ⋙ CategoryTheory.forget RingCat.{u}).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    exact (reflectsLimit_of_reflectsIsomorphisms F
      (CategoryTheory.forget RingCat.{u})).reflects hs

/-- Underlying sets reflect ring limits without a bound on the diagram universe. -/
private instance ringForgetReflectsLimits :
    ReflectsLimitsOfSize.{v, c} (CategoryTheory.forget RingCat.{u}) where
  reflectsLimitsOfShape := { reflectsLimit := ringForgetReflectsLimit _ }

/-- A limiting cone of underlying sets gives the original commutative-ring cone its limit law. -/
private theorem commRingForgetReflectsLimit {D : Type c} [Category.{v} D]
    (F : D ⥤ CommRingCat.{u}) : ReflectsLimit F (CategoryTheory.forget CommRingCat.{u}) where
  reflects {s} hs := by
    -- Local instance justification (proof-local temporary data): the supplied cone determines smallness of its own section type before constructing the commutative-ring limit.
    letI : HasLimit (F ⋙ CategoryTheory.forget CommRingCat.{u}) := ⟨_, hs⟩
    -- Local instance justification (proof-local temporary data): the section-type bound is obtained from this cone alone and supplies the actual commutative-ring limit.
    letI : Small.{u} (F ⋙ CategoryTheory.forget CommRingCat.{u}).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    exact (reflectsLimit_of_reflectsIsomorphisms F
      (CategoryTheory.forget CommRingCat.{u})).reflects hs

/-- Underlying sets reflect commutative-ring limits of every diagram size. -/
private instance commRingForgetReflectsLimits :
    ReflectsLimitsOfSize.{v, c} (CategoryTheory.forget CommRingCat.{u}) where
  reflectsLimitsOfShape := { reflectsLimit := commRingForgetReflectsLimit _ }

/-- Forgetting commutativity preserves limits without a bound on the diagram universe. -/
private instance commRingForgetPreservesLimits :
    PreservesLimitsOfSize.{v, c} (forget₂ CommRingCat.{u} RingCat.{u}) := by
  -- Local instance justification (defeq pin): identify the composite forgetful functor with the underlying-set right adjoint while transferring its limit-preservation law.
  letI : PreservesLimitsOfSize.{v, c}
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ CategoryTheory.forget RingCat.{u}) :=
    inferInstanceAs (PreservesLimitsOfSize.{v, c} (CategoryTheory.forget CommRingCat.{u}))
  exact preservesLimits_of_reflects_of_preserves _ (CategoryTheory.forget RingCat.{u})

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- Lifting the coefficient rings preserves the sheaf condition on an arbitrary site. -/
private theorem ring_isSheaf (R : Sheaf J RingCat.{u}) :
    Presheaf.IsSheaf J (R.obj ⋙ UniverseLift.ringFunctor) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget RingCat.{u + 1})
  change Presheaf.IsSheaf J ((R.obj ⋙ CategoryTheory.forget RingCat.{u}) ⋙ uliftFunctor.{u + 1})
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor J
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J R.obj (CategoryTheory.forget RingCat.{u}) R.property))

/-- The coefficient sheaf obtained by applying `ULift` to every ring of sections. -/
def ring (R : Sheaf J RingCat.{u}) : Sheaf J RingCat.{u + 1} :=
  ⟨R.obj ⋙ UniverseLift.ringFunctor, ring_isSheaf R⟩

/-- Lifting commutative coefficient rings preserves the sheaf condition. -/
private theorem commRing_isSheaf (O : Sheaf J CommRingCat.{u}) :
    Presheaf.IsSheaf J (O.obj ⋙ CommRingCat.universeLift.{u, u + 1}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget CommRingCat.{u + 1})
  change Presheaf.IsSheaf J ((O.obj ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙ uliftFunctor.{u + 1})
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor J
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J O.obj (CategoryTheory.forget CommRingCat.{u}) O.property))

/-- The commutative coefficient sheaf with section rings lifted by `ULift`. -/
def commRing (O : Sheaf J CommRingCat.{u}) : Sheaf J CommRingCat.{u + 1} :=
  ⟨O.obj ⋙ CommRingCat.universeLift.{u, u + 1}, commRing_isSheaf O⟩

/-- Forgetting commutativity before or after lifting gives the same coefficient sheaf. -/
def commRingForgetIso (O : Sheaf J CommRingCat.{u}) :
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (commRing O) ≅
      ring ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by ext x; rfl))

/-- A module's original additive presheaf with scalars acting through `ULift.down`. -/
private def forwardPresheaf (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u + 1} R) :
    PresheafOfModules.{u + 1} (ring R).obj where
  obj V := (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj V) ≃+* R.obj.obj V).toRingHom).obj (M.val.obj V)
  map {V W} f := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj V) ≃+* R.obj.obj V).toRingHom).obj (M.val.obj V))
    (Y := (ModuleCat.restrictScalars ((ring R).obj.map f).hom).obj
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj W) ≃+* R.obj.obj W).toRingHom).obj (M.val.obj W)))
    { toFun := M.val.map f
      map_add' := (M.val.map f).hom.map_add
      map_smul' := fun r m ↦ M.val.map_smul f r.down m }
  map_id V := by
    ext m
    exact ConcreteCategory.congr_hom (M.val.presheaf.map_id V) m
  map_comp f g := by
    ext m
    exact M.val.map_comp_apply f g m

/-- Coefficient lifting retains the module carriers, restrictions, and morphism functions. -/
private def forward (R : Sheaf J RingCat.{u}) :
    SheafOfModules.{u + 1} R ⥤ SheafOfModules.{u + 1} (ring R) where
  obj M := ⟨forwardPresheaf R M, M.isSheaf⟩
  map {M N} f :=
    { val :=
        { app V := ModuleCat.ofHom
            (X := (forwardPresheaf R M).obj V) (Y := (forwardPresheaf R N).obj V)
            { toFun := f.val.app V
              map_add' := (f.val.app V).hom.map_add
              map_smul' := fun r m ↦ (f.val.app V).hom.map_smul r.down m }
          naturality := fun g ↦ by
            ext m
            exact PresheafOfModules.naturality_apply f.val g m } }
  map_id M := by ext V m; rfl
  map_comp f g := by ext V m; rfl

/-- A lifted-coefficient module with the original scalars acting through `ULift.up`. -/
private def inversePresheaf (R : Sheaf J RingCat.{u})
    (N : SheafOfModules.{u + 1} (ring R)) : PresheafOfModules.{u + 1} R.obj where
  obj V := (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj V) ≃+* R.obj.obj V).symm.toRingHom).obj (N.val.obj V)
  map {V W} f := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj V) ≃+* R.obj.obj V).symm.toRingHom).obj (N.val.obj V))
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{u + 1} (R.obj.obj W) ≃+* R.obj.obj W).symm.toRingHom).obj (N.val.obj W)))
    { toFun := N.val.map f
      map_add' := (N.val.map f).hom.map_add
      map_smul' := fun r m ↦ N.val.map_smul f (ULift.up r) m }
  map_id V := by
    ext m
    exact ConcreteCategory.congr_hom (N.val.presheaf.map_id V) m
  map_comp f g := by
    ext m
    exact N.val.map_comp_apply f g m

/-- Lowering lifted coefficients retains the additive functions on restrictions and morphisms. -/
private def inverse (R : Sheaf J RingCat.{u}) :
    SheafOfModules.{u + 1} (ring R) ⥤ SheafOfModules.{u + 1} R where
  obj N := ⟨inversePresheaf R N, N.isSheaf⟩
  map {M N} f :=
    { val :=
        { app V := ModuleCat.ofHom
            (X := (inversePresheaf R M).obj V) (Y := (inversePresheaf R N).obj V)
            { toFun := f.val.app V
              map_add' := (f.val.app V).hom.map_add
              map_smul' := fun r m ↦ (f.val.app V).hom.map_smul (ULift.up r) m }
          naturality := fun g ↦ by
            ext m
            exact PresheafOfModules.naturality_apply f.val g m } }
  map_id M := by ext V m; rfl
  map_comp f g := by ext V m; rfl

/-- Lifting and lowering coefficients are inverse through identity functions on sections. -/
def equivalence (R : Sheaf J RingCat.{u}) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} (ring R) where
  functor := forward R
  inverse := inverse R
  unitIso := NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom (X := M.val.obj V)
            (Y := (inversePresheaf R ((forward R).obj M)).obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom (Y := M.val.obj V)
            (X := (inversePresheaf R ((forward R).obj M)).obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext m; rfl
          inv_hom_id := by ext m; rfl }) (fun {_ _} f ↦ by ext m; rfl)))
    (fun f ↦ by ext V m; rfl)
  counitIso := NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget (ring R)).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom (Y := N.val.obj V)
            (X := (forwardPresheaf R ((inverse R).obj N)).obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom (X := N.val.obj V)
            (Y := (forwardPresheaf R ((inverse R).obj N)).obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext m; rfl
          inv_hom_id := by ext m; rfl }) (fun {_ _} f ↦ by ext m; rfl)))
    (fun f ↦ by ext V m; rfl)
  functor_unitIso_comp M := by ext V m; rfl

/-- Lifting coefficients leaves every type of module sections unchanged. -/
theorem equivalence_obj_carrier (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u + 1} R) (V : Cᵒᵖ) :
    (((equivalence R).functor.obj M).val.obj V : Type (u + 1)) = M.val.obj V := rfl

/-- A coefficient-lifted module morphism has the original component function. -/
theorem equivalence_map_apply (R : Sheaf J RingCat.{u})
    {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N) (V : Cᵒᵖ) (m : M.val.obj V) :
    (((equivalence R).functor.map f).val.app V) m = f.val.app V m := rfl

/-- Lowering coefficients leaves every type of module sections unchanged. -/
theorem inverse_obj_carrier (R : Sheaf J RingCat.{u})
    (N : SheafOfModules.{u + 1} (ring R)) (V : Cᵒᵖ) :
    (((equivalence R).inverse.obj N).val.obj V : Type (u + 1)) = N.val.obj V := rfl

/-- Lowering coefficients leaves every module-morphism component function unchanged. -/
theorem inverse_map_apply (R : Sheaf J RingCat.{u})
    {M N : SheafOfModules.{u + 1} (ring R)} (f : M ⟶ N) (V : Cᵒᵖ) (m : M.val.obj V) :
    (((equivalence R).inverse.map f).val.app V) m = f.val.app V m := rfl

end SheafOfModules.CoefficientLift

